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
      , contents = Seq.tabulate (fn i => String.sub (s, i)) (String.size s)
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

  fun stringTokSpace t =
    mkToken ("\"" ^ Token.toString (stripToken t) ^ " \"")

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
      , exps = Seq.singleton exp
      , delims = Seq.empty ()
      , endd = mkReservedToken End
      }

  fun tupleExp [] = unitExp
    | tupleExp [Const tok] = Const tok
    | tupleExp (exps as _ :: tail) =
        Tuple
          { left = openParenTok
          , elems = Seq.fromList exps
          , delims = Seq.fromList (List.map (fn _ => commaTok) tail)
          , right = closeParenTok
          }

  fun recordExp params =
    Record
      { left = mkReservedToken OpenCurlyBracket
      , elems = Seq.fromList
          (List.map (fn (a, b) => RecordRow {lab = a, eq = equalTok, exp = b})
             params)
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length params - 1))
      , right = mkReservedToken CloseCurlyBracket
      }

  fun listExp exps =
    List
      { left = mkReservedToken OpenSquareBracket
      , elems = Seq.fromList exps
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length exps - 1))
      , right = mkReservedToken CloseSquareBracket
      }

  fun appExp [] = raise Fail "Empty application"
    | appExp [exp] = exp
    | appExp (exp :: exps) =
        List.foldl (fn (e, acc) => App {left = acc, right = e}) exp exps

  fun singleFnExp pat exp =
    Fn
      { fnn = mkReservedToken Token.Fn
      , elems = Seq.singleton {pat = pat, arrow = fatArrowTok, exp = exp}
      , delims = Seq.empty ()
      , optbar = NONE
      }

  fun multFnExp tups =
    Fn
      { fnn = mkReservedToken Token.Fn
      , elems = Seq.fromList
          (List.map
             (fn (pat, exp) => {pat = pat, arrow = fatArrowTok, exp = exp}) tups)
      , delims = Seq.tabulate (fn _ => orTok) (Int.max
          (0, List.length tups - 1))
      , optbar = NONE
      }

  fun parensExp (Const tok) = Const tok
    | parensExp exp =
        Parens {left = openParenTok, exp = exp, right = closeParenTok}

  fun infixLExp _ [] = raise Fail "Empty infixl expression"
    | infixLExp _ [exp] = exp
    | infixLExp opp (exp :: exps) =
        List.foldl (fn (e, acc) => Infix {left = acc, id = opp, right = e}) exp
          exps

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
      , elems = Seq.singleton {recc = NONE, pat = pat, eq = equalTok, exp = exp}
      , delims = Seq.empty ()
      }

  fun valDecs l =
    DecVal
      { vall = mkReservedToken Val
      , tyvars = SyntaxSeq.Empty
      , elems = Seq.fromList
          (List.map
             (fn (recc, pat, exp) =>
                { recc = if recc then SOME recTok else NONE
                , pat = pat
                , eq = equalTok
                , exp = exp
                }) l)
      , delims = Seq.tabulate (fn _ => andReservedTok) (Int.max
          (0, List.length l - 1))
      }

  fun multDec decs =
    DecMultiple
      { elems = Seq.fromList decs
      , delims = Seq.fromList (List.map (fn _ => NONE) decs)
      }

  fun singleFunDec tok args exp =
    DecFun
      { funn = mkReservedToken Fun
      , tyvars = SyntaxSeq.Empty
      , fvalbind =
          { elems = Seq.singleton
              { elems = Seq.singleton
                  { fname_args =
                      PrefixedFun
                        {opp = NONE, id = tok, args = Seq.fromList args}
                  , ty = NONE
                  , eq = equalTok
                  , exp = exp
                  }
              , delims = Seq.empty ()
              , optbar = NONE
              }
          , delims = Seq.empty ()
          }
      }

  fun multFunDec funs =
    DecFun
      { funn = mkReservedToken Fun
      , tyvars = SyntaxSeq.Empty
      , fvalbind =
          { elems = Seq.fromList
              (List.map
                 (fn cases =>
                    { elems = Seq.fromList
                        (List.map
                           (fn (tok, args, exp) =>
                              { fname_args =
                                  PrefixedFun
                                    { opp = NONE
                                    , id = tok
                                    , args = Seq.fromList args
                                    }
                              , ty = NONE
                              , eq = equalTok
                              , exp = exp
                              }) cases)
                    , delims = Seq.tabulate (fn _ => orTok) (Int.max
                        (0, List.length cases - 1))
                    , optbar = NONE
                    }) funs)
          , delims = Seq.tabulate (fn _ => andKeyTok) (Int.max
              (0, List.length funs - 1))
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
  fun localDecs decs body =
    case decs of
      [] => body
    | _ => localDec (multDec decs) body

  val genericDec = DecOpen {openn = openTok, elems = Seq.singleton genericTok}
  val tieDec = DecOpen {openn = openTok, elems = Seq.singleton tieTok}

  fun destructRecordPat patTokens =
    Pat.Record
      { left = mkReservedToken OpenCurlyBracket
      , elems = Seq.fromList
          (List.map (fn tok => Pat.LabAsPat {id = tok, ty = NONE, aspat = NONE})
             patTokens)
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length patTokens - 1))
      , right = mkReservedToken CloseCurlyBracket
      }

  fun destructRecordPat' rows =
    Pat.Record
      { left = mkReservedToken OpenCurlyBracket
      , elems = Seq.fromList
          (List.map
             (fn (lab, pat) =>
                Pat.LabEqPat {lab = lab, eq = equalTok, pat = pat}) rows)
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length rows - 1))
      , right = mkReservedToken CloseCurlyBracket
      }

  fun destructTuplePat [Pat.Const tok] = Pat.Const tok
    | destructTuplePat pats =
        Pat.Tuple
          { left = openParenTok
          , elems = Seq.fromList pats
          , delims = Seq.tabulate (fn _ => commaTok) (Int.max
              (0, List.length pats - 1))
          , right = closeParenTok
          }

  fun destructInfixLPat _ [] =
        raise Fail "Destructing empty infixl pattern"
    | destructInfixLPat _ [pat] = pat
    | destructInfixLPat opp (pat :: pats) =
        List.foldl (fn (p, acc) => Pat.Infix {left = acc, id = opp, right = p})
          pat pats

  fun destructListPat pats =
    Pat.List
      { left = mkReservedToken OpenSquareBracket
      , elems = Seq.fromList pats
      , delims = Seq.fromList
          (case pats of
             [] => []
           | _ :: pats => List.map (fn _ => commaTok) pats)
      , right = mkReservedToken CloseSquareBracket
      }

  fun destructConPat tok pat =
    Pat.Con {opp = NONE, id = MaybeLongToken.make tok, atpat = pat}

  val wildPat = Pat.Wild underTok

  fun parensTy ty =
    Ty.Parens {left = openParenTok, ty = ty, right = closeParenTok}
end
