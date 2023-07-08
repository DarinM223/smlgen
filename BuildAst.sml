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
  val andReservedTok = mkReservedToken And
  val recTok = mkReservedToken Rec
  val orTok = mkReservedToken Bar
  val andKeyTok = mkReservedToken And
  val andTok = mkToken "&"
  val quesTok = mkToken "?"
  val prodTok = mkToken "*`"
  val fatArrowTok = mkReservedToken FatArrow
  val genericTok = MaybeLongToken.make (mkToken "Generic")
  val tieTok = MaybeLongToken.make (mkToken "Tie")
  val openTok = mkReservedToken Open
  val underTok = mkReservedToken Underscore
  val tTok = mkToken "t"
  val falseTok = mkToken "false"
  val trueTok = mkToken "true"
  val openParenTok = mkReservedToken OpenParen
  val closeParenTok = mkReservedToken CloseParen

  val unitExp = Unit {left = openParenTok, right = closeParenTok}

  fun singleLetExp dec exp =
    LetInEnd
      { lett = mkReservedToken Let
      , dec = dec
      , inn = mkReservedToken In
      , exps = ArraySlice.full (Array.fromList [exp])
      , delims = ArraySlice.full (Array.fromList [])
      , endd = mkReservedToken End
      }

  fun tupleExp [Const tok] = Const tok
    | tupleExp exps =
        Tuple
          { left = openParenTok
          , elems = ArraySlice.full (Array.fromList exps)
          , delims = ArraySlice.full (Array.fromList
              (List.map (fn _ => commaTok) (List.tl exps)))
          , right = closeParenTok
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

  fun listExp exps =
    List
      { left = mkReservedToken OpenSquareBracket
      , elems = ArraySlice.full (Array.fromList exps)
      , delims = ArraySlice.full (Array.fromList
          (List.map (fn _ => commaTok) (List.tl exps)))
      , right = mkReservedToken CloseSquareBracket
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

  fun parensExp (Const tok) = Const tok
    | parensExp exp =
        Parens {left = openParenTok, exp = exp, right = closeParenTok}

  fun infixLExp opp exps =
    List.foldl (fn (e, acc) => Infix {left = acc, id = opp, right = e})
      (List.hd exps) (List.tl exps)

  val unitPat = Pat.Unit {left = openParenTok, right = closeParenTok}

  fun parensPat (pat as Pat.Const _) = pat
    | parensPat (pat as Pat.Tuple _) = pat
    | parensPat (pat as Pat.Record _) = pat
    | parensPat pat =
        Pat.Parens {left = openParenTok, pat = pat, right = closeParenTok}

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

  fun valDecs l =
    DecVal
      { vall = mkReservedToken Val
      , tyvars = SyntaxSeq.Empty
      , elems = ArraySlice.full (Array.fromList
          (List.map
             (fn (recc, pat, exp) =>
                { recc = if recc then SOME recTok else NONE
                , pat = pat
                , eq = equalTok
                , exp = exp
                }) l))
      , delims = ArraySlice.full (Array.fromList
          (List.map (fn _ => andReservedTok) (List.tl l)))
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

  fun multFunDec funs =
    DecFun
      { funn = mkReservedToken Fun
      , tyvars = SyntaxSeq.Empty
      , fvalbind =
          { elems = ArraySlice.full (Array.fromList
              (List.map
                 (fn cases =>
                    { elems = ArraySlice.full (Array.fromList
                        (List.map
                           (fn (tok, args, exp) =>
                              { fname_args = PrefixedFun
                                  { opp = NONE
                                  , id = tok
                                  , args = ArraySlice.full (Array.fromList args)
                                  }
                              , ty = NONE
                              , eq = equalTok
                              , exp = exp
                              }) cases))
                    , delims = ArraySlice.full (Array.fromList
                        (List.map (fn _ => orTok) (List.tl cases)))
                    , optbar = NONE
                    }) funs))
          , delims = ArraySlice.full (Array.fromList
              (List.map (fn _ => andKeyTok) (List.tl funs)))
          }
      }

  fun localDec dec body =
    DecLocal
      { locall = mkReservedToken Local
      , left_dec = dec
      , inn = mkReservedToken In
      , right_dec = body
      , endd = mkReservedToken End
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

  fun destructRecordPat' rows =
    Pat.Record
      { left = mkReservedToken OpenCurlyBracket
      , elems = ArraySlice.full (Array.fromList
          (List.map
             (fn (lab, pat) =>
                Pat.LabEqPat {lab = lab, eq = equalTok, pat = pat}) rows))
      , delims = ArraySlice.full (Array.fromList (List.tl
          (List.map (fn _ => commaTok) rows)))
      , right = mkReservedToken CloseCurlyBracket
      }

  fun destructTuplePat [Pat.Const tok] = Pat.Const tok
    | destructTuplePat pats =
        Pat.Tuple
          { left = openParenTok
          , elems = ArraySlice.full (Array.fromList pats)
          , delims = ArraySlice.full (Array.fromList (List.tl
              (List.map (fn _ => commaTok) pats)))
          , right = closeParenTok
          }

  fun destructInfixLPat opp pats =
    List.foldl (fn (p, acc) => Pat.Infix {left = acc, id = opp, right = p})
      (List.hd pats) (List.tl pats)

  fun destructListPat pats =
    Pat.List
      { left = mkReservedToken OpenSquareBracket
      , elems = ArraySlice.full (Array.fromList pats)
      , delims = ArraySlice.full (Array.fromList
          (case pats of
             [] => []
           | _ => (List.tl (List.map (fn _ => commaTok) pats))))
      , right = mkReservedToken CloseSquareBracket
      }

  val wildPat = Pat.Wild underTok

  fun parensTy ty =
    Ty.Parens {left = openParenTok, ty = ty, right = closeParenTok}
end
