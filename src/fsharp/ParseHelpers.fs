// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

module FSharp.Compiler.ParseHelpers

open System
open System.Globalization
open FSharp.Compiler.AbstractIL
open FSharp.Compiler.ErrorLogger
open FSharp.Compiler.Features
open FSharp.Compiler.Text
open FSharp.Compiler.Text.Pos
open FSharp.Compiler.Text.Range
open FSharp.Compiler.SyntaxTreeOps
open FSharp.Compiler.UnicodeLexing
open FSharp.Compiler.XmlDoc
open Internal.Utilities.Text.Lexing
open Internal.Utilities.Text.Parsing

//------------------------------------------------------------------------
// Parsing: Error recovery exception for fsyacc
//------------------------------------------------------------------------

/// The error raised by the parse_error_rich function, which is called by the parser engine
/// when a syntax error occurs. The first object is the ParseErrorContext which contains a dump of
/// information about the grammar at the point where the error occurred, e.g. what tokens
/// are valid to shift next at that point in the grammar. This information is processed in CompileOps.fs.
[<NoEquality; NoComparison>]
exception SyntaxError of obj (* ParseErrorContext<_> *) * range: range

exception IndentationProblem of string * range

let warningStringOfCoords line column =
    sprintf "(%d:%d)" line (column + 1)

let warningStringOfPos (p: pos) =
    warningStringOfCoords p.Line p.Column

//------------------------------------------------------------------------
// Parsing: getting positions from the lexer
//------------------------------------------------------------------------

/// Get an F# compiler position from a lexer position
let posOfLexPosition (p: Position) =
    mkPos p.Line p.Column

/// Get an F# compiler range from a lexer range
let mkSynRange (p1: Position) (p2: Position) =
    mkFileIndexRange p1.FileIndex (posOfLexPosition p1) (posOfLexPosition p2)

type LexBuffer<'Char> with
    member lexbuf.LexemeRange  = mkSynRange lexbuf.StartPos lexbuf.EndPos

/// Get the range corresponding to the result of a grammar rule while it is being reduced
let lhs (parseState: IParseState) =
    let p1 = parseState.ResultStartPosition
    let p2 = parseState.ResultEndPosition
    mkSynRange p1 p2

/// Get the range covering two of the r.h.s. symbols of a grammar rule while it is being reduced
let rhs2 (parseState: IParseState) i j =
    let p1 = parseState.InputStartPosition i
    let p2 = parseState.InputEndPosition j
    mkSynRange p1 p2

/// Get the range corresponding to one of the r.h.s. symbols of a grammar rule while it is being reduced
let rhs parseState i = rhs2 parseState i i

type IParseState with

    /// Get the generator used for compiler-generated argument names.
    member x.SynArgNameGenerator =
        let key = "SynArgNameGenerator"
        let bls = x.LexBuffer.BufferLocalStore
        let gen =
            match bls.TryGetValue key with
            | true, gen -> gen
            | _ ->
                let gen = box (SynArgNameGenerator())
                bls.[key] <- gen
                gen
        gen :?> SynArgNameGenerator

    /// Reset the generator used for compiler-generated argument names.
    member x.ResetSynArgNameGenerator() = x.SynArgNameGenerator.Reset()

//------------------------------------------------------------------------
// Parsing: grabbing XmlDoc
//------------------------------------------------------------------------

/// XmlDoc F# lexer/parser state, held in the BufferLocalStore for the lexer.
/// This is the only use of the lexer BufferLocalStore in the codebase.
module LexbufLocalXmlDocStore =
    // The key into the BufferLocalStore used to hold the current accumulated XmlDoc lines
    let private xmlDocKey = "XmlDoc"

    let ClearXmlDoc (lexbuf: Lexbuf) =
        lexbuf.BufferLocalStore.[xmlDocKey] <- box (XmlDocCollector())

    /// Called from the lexer to save a single line of XML doc comment.
    let SaveXmlDocLine (lexbuf: Lexbuf, lineText, range: range) =
        let collector =
            match lexbuf.BufferLocalStore.TryGetValue xmlDocKey with
            | true, collector -> collector
            | _ ->
                let collector = box (XmlDocCollector())
                lexbuf.BufferLocalStore.[xmlDocKey] <- collector
                collector
        let collector = unbox<XmlDocCollector>(collector)
        collector.AddXmlDocLine(lineText, range)

    /// Called from the parser each time we parse a construct that marks the end of an XML doc comment range,
    /// e.g. a 'type' declaration. The markerRange is the range of the keyword that delimits the construct.
    let GrabXmlDocBeforeMarker (lexbuf: Lexbuf, markerRange: range)  =
        match lexbuf.BufferLocalStore.TryGetValue xmlDocKey with
        | true, collector ->
            let collector = unbox<XmlDocCollector>(collector)
            PreXmlDoc.CreateFromGrabPoint(collector, markerRange.End)
        | _ ->
            PreXmlDoc.Empty


//------------------------------------------------------------------------
// Parsing/lexing: status of #if/#endif processing in lexing, used for continutations
// for whitespace tokens in parser specification.
//------------------------------------------------------------------------

type LexerIfdefStackEntry =
    | IfDefIf
    | IfDefElse

/// Represents the active #if/#else blocks
type LexerIfdefStackEntries = (LexerIfdefStackEntry * range) list

type LexerIfdefStack = LexerIfdefStackEntries

/// Specifies how the 'endline' function in the lexer should continue after
/// it reaches end of line or eof. The options are to continue with 'token' function
/// or to continue with 'skip' function.
type LexerEndlineContinuation =
    | Token 
    | Skip of int * range: range

type LexerIfdefExpression =
    | IfdefAnd of LexerIfdefExpression*LexerIfdefExpression
    | IfdefOr of LexerIfdefExpression*LexerIfdefExpression
    | IfdefNot of LexerIfdefExpression
    | IfdefId of string

let rec LexerIfdefEval (lookup: string -> bool) = function
    | IfdefAnd (l, r)    -> (LexerIfdefEval lookup l) && (LexerIfdefEval lookup r)
    | IfdefOr (l, r)     -> (LexerIfdefEval lookup l) || (LexerIfdefEval lookup r)
    | IfdefNot e        -> not (LexerIfdefEval lookup e)
    | IfdefId id        -> lookup id

//------------------------------------------------------------------------
// Parsing: continuations for whitespace tokens
//------------------------------------------------------------------------

[<RequireQualifiedAccess>]
type LexerStringStyle =
    | Verbatim
    | TripleQuote
    | SingleQuote

[<RequireQualifiedAccess; Struct>]
type LexerStringKind =
    { IsByteString: bool
      IsInterpolated: bool
      IsInterpolatedFirst: bool }
    static member String = { IsByteString = false; IsInterpolated = false; IsInterpolatedFirst=false }
    static member ByteString = { IsByteString = true; IsInterpolated = false; IsInterpolatedFirst=false }
    static member InterpolatedStringFirst = { IsByteString = false; IsInterpolated = true; IsInterpolatedFirst=true }
    static member InterpolatedStringPart = { IsByteString = false; IsInterpolated = true; IsInterpolatedFirst=false }

/// Represents the degree of nesting of '{..}' and the style of the string to continue afterwards, in an interpolation fill.
/// Nesting counters and styles of outer interpolating strings are pushed on this stack.
type LexerInterpolatedStringNesting = (int * LexerStringStyle * range) list

/// The parser defines a number of tokens for whitespace and
/// comments eliminated by the lexer.  These carry a specification of
/// a continuation for the lexer for continued processing after we've dealt with
/// the whitespace.
[<RequireQualifiedAccess>]
[<NoComparison; NoEquality>]
type LexerContinuation =
    | Token of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting
    | IfDefSkip of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * int * range: range
    | String of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * style: LexerStringStyle * kind: LexerStringKind * range: range
    | Comment of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * int * range: range
    | SingleLineComment of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * int * range: range
    | StringInComment of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * style: LexerStringStyle * int * range: range
    | MLOnly of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * range: range
    | EndLine of ifdef: LexerIfdefStackEntries * nesting: LexerInterpolatedStringNesting * LexerEndlineContinuation

    static member Default = LexCont.Token([],[])

    member x.LexerIfdefStack =
        match x with
        | LexCont.Token (ifdef=ifd)
        | LexCont.IfDefSkip (ifdef=ifd)
        | LexCont.String (ifdef=ifd)
        | LexCont.Comment (ifdef=ifd)
        | LexCont.SingleLineComment (ifdef=ifd)
        | LexCont.StringInComment (ifdef=ifd)
        | LexCont.EndLine (ifdef=ifd)
        | LexCont.MLOnly (ifdef=ifd) -> ifd

    member x.LexerInterpStringNesting =
        match x with
        | LexCont.Token (nesting=nesting)
        | LexCont.IfDefSkip (nesting=nesting)
        | LexCont.String (nesting=nesting)
        | LexCont.Comment (nesting=nesting)
        | LexCont.SingleLineComment (nesting=nesting)
        | LexCont.StringInComment (nesting=nesting)
        | LexCont.EndLine (nesting=nesting)
        | LexCont.MLOnly (nesting=nesting) -> nesting

and LexCont = LexerContinuation

//------------------------------------------------------------------------
// Parse IL assembly code
//------------------------------------------------------------------------

let ParseAssemblyCodeInstructions s (isFeatureSupported: LanguageFeature -> bool) m : IL.ILInstr[] = 
#if NO_INLINE_IL_PARSER
    ignore s
    ignore isFeatureSupported

    errorR(Error((193, "Inline IL not valid in a hosted environment"), m))
    [| |]
#else
    try
        FSharp.Compiler.AbstractIL.Internal.AsciiParser.ilInstrs
           FSharp.Compiler.AbstractIL.Internal.AsciiLexer.token
           (UnicodeLexing.StringAsLexbuf(isFeatureSupported, s))
    with _ ->
      errorR(Error(FSComp.SR.astParseEmbeddedILError(), m)); [||]
#endif

let ParseAssemblyCodeType s (isFeatureSupported: Features.LanguageFeature -> bool) m =
    ignore s
    ignore isFeatureSupported

#if NO_INLINE_IL_PARSER
    errorR(Error((193, "Inline IL not valid in a hosted environment"), m))
    IL.EcmaMscorlibILGlobals.typ_Object
#else
    let isFeatureSupported (_featureId:LanguageFeature) = true
    try
        FSharp.Compiler.AbstractIL.Internal.AsciiParser.ilType
           FSharp.Compiler.AbstractIL.Internal.AsciiLexer.token
           (UnicodeLexing.StringAsLexbuf(isFeatureSupported, s))
    with RecoverableParseError ->
      errorR(Error(FSComp.SR.astParseEmbeddedILTypeError(), m));
      IL.EcmaMscorlibILGlobals.typ_Object
#endif

//--------------------------
// Integer parsing

// Parsing integers is common in bootstrap runs (parsing
// the parser tables, no doubt). So this is an optimized
// version of the F# core library parsing code with the call to "Trim"
// removed, which appears in profiling runs as a small but significant cost.

module Ranges =
    /// Whether valid as signed int8 when a minus sign is prepended, compares true to 0x80
    let isInt8BadMax x = 1 <<< 7 = x

    /// Whether valid as signed int16 when a minus sign is prepended, compares true to 0x8000
    let isInt16BadMax x = 1 <<< 15 = x

    /// Whether valid as signed int32 when a minus sign is prepended, compares as string against "2147483648".
    let isInt32BadMax = let max = string(1UL <<< 31) in fun s -> max = s

    /// Whether valid as signed int64 when a minus sign is prepended, compares as string against "9223372036854775808".
    let isInt64BadMax = let max = string(1UL <<< 63) in fun s -> max = s

let getSign32 (s:string) (p:byref<int>) l = 
    if (l >= p + 1 && s.[p] = '-') then
        p <- p + 1; -1 
    elif (l >= p + 1 && s.[p] = '+') then
        p <- p + 1; 1 
    else 1 

let isOXB c = 
    let c = Char.ToLowerInvariant c
    c = 'x' || c = 'o' || c = 'b'

let is0OXB (s:string) p l = 
    l >= p + 2 && s.[p] = '0' && isOXB s.[p+1]

let get0OXB (s:string) (p:byref<int>)  l = 
    if is0OXB s p l
    then let r = Char.ToLowerInvariant s.[p+1] in p <- p + 2; r
    else 'd' 

let parseBinaryUInt64 (s:string) = 
    Convert.ToUInt64(s, 2)

let parseOctalUInt64 (s:string) =
    Convert.ToUInt64(s, 8)

let parseSmallInt (errorLogger: ErrorLogger) m (s: string) =
    try
        let l = s.Length 
        let mutable p = 0 
        let sign = getSign32 s &p l 
        let specifier = get0OXB s &p l 
        match Char.ToLower(specifier,CultureInfo.InvariantCulture) with 
        | 'x' -> sign * (int32 (Convert.ToUInt32(UInt64.Parse(s.Substring(p), NumberStyles.AllowHexSpecifier,CultureInfo.InvariantCulture))))
        | 'b' -> sign * (int32 (Convert.ToUInt32(parseBinaryUInt64 (s.Substring(p)))))
        | 'o' -> sign * (int32 (Convert.ToUInt32(parseOctalUInt64  (s.Substring(p)))))
        | _ -> Int32.Parse(s, NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture)
    with _ ->
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideIntegerRange(), m))
        0

let parseInt32AllowMaxIntPlusOne (errorLogger: ErrorLogger) m s =
    // Allow <max_int+1> to parse as min_int.  Allowed only because we parse '-' as an operator. 
    if Ranges.isInt32BadMax s then 
        (Int32.MinValue,true) 
    else
        let n = 
            try int32 s 
            with _ ->  
                errorLogger.ErrorR(Error(FSComp.SR.lexOutsideThirtyTwoBitSigned(),m))
                0
        n, false

let parseInt32 (errorLogger: ErrorLogger) m s =
    let n, fail = parseInt32AllowMaxIntPlusOne errorLogger m s
    if fail then errorR(Error(FSComp.SR.lexOutsideThirtyTwoBitSigned(), m))
    n

let parseUInt32 (errorLogger: ErrorLogger) m (s: string) =
    let n = 
        try int64 s 
        with _ ->  
             errorLogger.ErrorR(Error(FSComp.SR.lexOutsideThirtyTwoBitUnsigned(), m))
             0L
    if n > UInt32.MaxValue || n < 0L then 
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideThirtyTwoBitUnsigned(), m))
        0u
    else
        uint32 (uint64 n)

let parseInt64AllowMaxIntPlusOne (errorLogger: ErrorLogger) m s =
    // Allow <max_int+1> to parse as min_int.  Stupid but allowed because we parse '-' as an operator. 
    if Ranges.isInt64BadMax s then 
        (Int64.MinValue,true) 
    else
        try int64 s, false
        with _ ->  
            errorLogger.ErrorR(Error(FSComp.SR.lexOutsideSixtyFourBitSigned(), m))
            0L, false

let parseInt64 (errorLogger: ErrorLogger) m s =
    let n, fail = parseInt64AllowMaxIntPlusOne errorLogger m s
    if fail then errorR(Error(FSComp.SR.lexOutsideSixtyFourBitSigned(), m))
    n

let parseUInt64 (errorLogger: ErrorLogger) m (s: string) =
    try uint64 s 
    with _ ->
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideSixtyFourBitUnsigned(), m))
        0UL

let parseNativeInt (errorLogger: ErrorLogger) m (s: string) =
    try 
        int64 s
    with _ ->  
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideNativeSigned(), m))
        0L

let parseUNativeInt (errorLogger: ErrorLogger) m (s: string) =
    try 
        uint64 s
    with _ ->  
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideNativeSigned(), m))
        0UL

let convSmallIntToSByteAllowMaxIntPlusOne (errorLogger: ErrorLogger) m n =
    if n > int SByte.MaxValue || n < int SByte.MinValue then
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideEightBitSigned(),m))
        0y,false
    elif Ranges.isInt8BadMax n then (sbyte(SByte.MinValue), true (* 'true' = 'bad'*) )
    else (sbyte n, false)

let convSmallIntToSByte (errorLogger: ErrorLogger) m n =
    let n, mpo = convSmallIntToSByteAllowMaxIntPlusOne errorLogger m n
    if mpo then errorR(Error(FSComp.SR.lexOutsideEightBitSigned(), m))
    n

let convSmallIntToInt16AllowMaxIntPlusOne (errorLogger: ErrorLogger) m n =
    if n > int Int16.MaxValue || n < int Int16.MinValue then
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideSixteenBitSigned(),m))
        0s,false
    elif n = Ranges.isInt16BadMax then (Int16.MinValue, true (* 'true' = 'bad'*) )
    else (int16 n, false)

let convSmallIntToInt16 (errorLogger: ErrorLogger) m n =
    let n, mpo = convSmallIntToInt16AllowMaxIntPlusOne errorLogger m n
    if mpo then errorR(Error(FSComp.SR.lexOutsideSixteenBitSigned(), m))
    n

let convSmallIntToByte (errorLogger: ErrorLogger) m n =
    if n > Byte.MaxValue || n < 0 then
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideEightBitUnsigned(), m))
        0uy
    else
        byte n

let convSmallIntToUInt16 (errorLogger: ErrorLogger) m n =
    if n > UInt16.MaxValue || n < 0 then
        errorLogger.ErrorR(Error(FSComp.SR.lexOutsideSixteenBitUnsigned(), m))
        0us
    else
        uint16 n

let parseDouble (errorLogger: ErrorLogger) m (s: string) =
    try float s with _ -> errorLogger.ErrorR(Error(FSComp.SR.lexInvalidFloat(), m)); 0.0

let parseSingle (errorLogger: ErrorLogger) m (s: string) =
    try float32 s with _ -> errorLogger.ErrorR(Error(FSComp.SR.lexInvalidFloat(), m)); 0.0f

let parseDecimal (errorLogger: ErrorLogger) m (s: string) =
    try 
        // This implements a range check for decimal literals 
        let d = System.Decimal.Parse(s,NumberStyles.AllowExponent ||| NumberStyles.Number, CultureInfo.InvariantCulture)
        d 
    with e ->
        errorLogger.ErrorR(Error(FSComp.SR.lexOusideDecimal(), m))
        decimal 0
