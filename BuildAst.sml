structure BuildAst =
struct
  open Token
  open Ast
  open Ast.Exp

  type constr =
    { arg: {off: Token.token, ty: Ty.ty} option
    , id: Token.token
    , opp: Token.token option
    }

  fun stripToken tok =
    case Token.prevToken tok of
      SOME tok => Option.valOf (Token.nextTokenNotCommentOrWhitespace tok)
    | NONE => tok

  fun mkSource (s: string) : Source.t =
    Source.make
      { fileName = FilePath.fromFields ["new"]
      , contents = ArraySlice.full (Array.tabulate (String.size s, fn i =>
          String.sub (s, i)))
      }

  fun mkToken (s: string) : Token.t =
    Token.fromPre (Token.Pretoken.make (mkSource s) Token.Identifier)

  fun mkReservedToken (r: Token.reserved) : Token.t =
    Token.fromPre
      (Token.Pretoken.reserved (mkSource (Token.reservedToString r)) r)

  fun appendTokens t1 t2 =
    mkToken (Token.toString (stripToken t1) ^ Token.toString (stripToken t2))

  fun stringTok t =
    mkToken ("\"" ^ Token.toString (stripToken t) ^ "\"")

  val equalTok = mkReservedToken Equal
  val commaTok = mkReservedToken Comma
  val orTok = mkReservedToken Bar
  val andTok = mkToken "&"
  val quesTok = mkToken "?"
  val prodTok = mkToken "*`"
  val fatArrowTok = mkReservedToken FatArrow
  val genericTok = MaybeLongToken.make (mkToken "Generic")
  val tieTok = MaybeLongToken.make (mkToken "Tie")
  val openTok = mkReservedToken Open
  val underTok = mkReservedToken Underscore

  val unitExp =
    Unit {left = mkReservedToken OpenParen, right = mkReservedToken CloseParen}

  fun singleLetExp dec exp =
    LetInEnd
      { lett = mkReservedToken Let
      , dec = dec
      , inn = mkReservedToken In
      , exps = ArraySlice.full (Array.fromList [exp])
      , delims = ArraySlice.full (Array.fromList [])
      , endd = mkReservedToken End
      }

  fun tupleExp exps =
    Tuple
      { left = mkReservedToken OpenParen
      , elems = ArraySlice.full (Array.fromList exps)
      , delims = ArraySlice.full (Array.fromList
          (List.map (fn _ => commaTok) (List.tl exps)))
      , right = mkReservedToken CloseParen
      }

  fun recordExp params =
    Record
      { left = mkReservedToken OpenCurlyBracket
      , elems = ArraySlice.full (Array.fromList
          (List.map (fn (a, b) => RecordRow {lab = a, eq = equalTok, exp = b})
             params))
      , delims =
          (ArraySlice.full o Array.fromList o List.map (fn _ => commaTok)
           o List.tl) params
      , right = mkReservedToken CloseCurlyBracket
      }

  fun appExp exps =
    List.foldl (fn (e, acc) => App {left = acc, right = e}) (List.hd exps)
      (List.tl exps)

  fun singleFnExp pat exp =
    Fn
      { fnn = mkReservedToken Token.Fn
      , elems = ArraySlice.full
          (Array.fromList [{pat = pat, arrow = fatArrowTok, exp = exp}])
      , delims = ArraySlice.full (Array.fromList [])
      , optbar = NONE
      }

  fun multFnExp tups =
    Fn
      { fnn = mkReservedToken Token.Fn
      , elems = ArraySlice.full (Array.fromList
          (List.map
             (fn (pat, exp) => {pat = pat, arrow = fatArrowTok, exp = exp}) tups))
      , delims = ArraySlice.full (Array.fromList
          (List.map (fn _ => orTok) (List.tl tups)))
      , optbar = NONE
      }

  fun parensExp exp =
    Parens
      { left = mkReservedToken OpenParen
      , exp = exp
      , right = mkReservedToken CloseParen
      }

  fun infixLExp opp exps =
    List.foldl (fn (e, acc) => Infix {left = acc, id = opp, right = e})
      (List.hd exps) (List.tl exps)

  val unitPat =
    Pat.Unit
      {left = mkReservedToken OpenParen, right = mkReservedToken CloseParen}

  fun parensPat pat =
    Pat.Parens
      { left = mkReservedToken OpenParen
      , pat = pat
      , right = mkReservedToken CloseParen
      }

  fun identPat t =
    Pat.Ident {opp = NONE, id = MaybeLongToken.make t}

  fun conPat con pat =
    Pat.Con {opp = NONE, id = MaybeLongToken.make con, atpat = pat}

  fun valDec pat exp =
    DecVal
      { vall = mkReservedToken Val
      , tyvars = SyntaxSeq.Empty
      , elems = ArraySlice.full (Array.fromList
          [{recc = NONE, pat = pat, eq = equalTok, exp = exp}])
      , delims = ArraySlice.full (Array.fromList [])
      }

  fun multDec decs =
    DecMultiple
      { elems = (ArraySlice.full o Array.fromList) decs
      , delims =
          (ArraySlice.full o Array.fromList o List.map (fn _ => NONE)) decs
      }

  fun singleFunDec tok args exp =
    DecFun
      { funn = mkReservedToken Fun
      , tyvars = SyntaxSeq.Empty
      , fvalbind =
          { elems = ArraySlice.full (Array.fromList
              [{ elems = ArraySlice.full (Array.fromList
                   [{ fname_args = PrefixedFun
                        { opp = NONE
                        , id = tok
                        , args = ArraySlice.full (Array.fromList args)
                        }
                    , ty = NONE
                    , eq = equalTok
                    , exp = exp
                    }])
               , delims = ArraySlice.full (Array.fromList [])
               , optbar = NONE
               }])
          , delims = ArraySlice.full (Array.fromList [])
          }
      }

  val genericDec = DecOpen
    {openn = openTok, elems = ArraySlice.full (Array.fromList [genericTok])}
  val tieDec = DecOpen
    {openn = openTok, elems = ArraySlice.full (Array.fromList [tieTok])}

  fun destructRecordPat patTokens =
    Pat.Record
      { left = mkReservedToken OpenCurlyBracket
      , elems = ArraySlice.full (Array.fromList
          (List.map (fn tok => Pat.LabAsPat {id = tok, ty = NONE, aspat = NONE})
             patTokens))
      , delims = ArraySlice.full (Array.fromList (List.tl
          (List.map (fn _ => commaTok) patTokens)))
      , right = mkReservedToken CloseCurlyBracket
      }

  fun destructTuplePat pats =
    Pat.Tuple
      { left = mkReservedToken OpenParen
      , elems = ArraySlice.full (Array.fromList pats)
      , delims = ArraySlice.full (Array.fromList (List.tl
          (List.map (fn _ => commaTok) pats)))
      , right = mkReservedToken CloseParen
      }

  fun destructInfixLPat opp pats =
    List.foldl (fn (p, acc) => Pat.Infix {left = acc, id = opp, right = p})
      (List.hd pats) (List.tl pats)

  val wildPat = Pat.Wild underTok
end
