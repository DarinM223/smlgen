structure TokenUtils :> TOKEN_UTILS =
struct
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
end

structure Tokens :> TOKENS =
struct
  open Token TokenUtils
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
  val structureTok = mkReservedToken Structure
  val structTok = mkReservedToken Struct
  val letTok = mkReservedToken Let
  val inTok = mkReservedToken In
  val endTok = mkReservedToken End
  val datatypeTok = mkReservedToken Datatype
  val openCurlyTok = mkReservedToken OpenCurlyBracket
  val closeCurlyTok = mkReservedToken CloseCurlyBracket
  val openSquareTok = mkReservedToken OpenSquareBracket
  val closeSquareTok = mkReservedToken CloseSquareBracket
  val fnTok = mkReservedToken Fn
  val valTok = mkReservedToken Val
  val funTok = mkReservedToken Fun
  val localTok = mkReservedToken Local
  val caseTok = mkReservedToken Case
  val ofTok = mkReservedToken Of
  val andalsoTok = mkReservedToken Andalso
end

structure BuildAst :> BUILD_AST =
struct
  open Ast Ast.Exp Tokens

  type constr =
    { arg: {off: Token.token, ty: Ty.ty} option
    , id: Token.token
    , opp: Token.token option
    }

  val unitExp = Unit {left = openParenTok, right = closeParenTok}

  fun singleLetExp dec exp =
    LetInEnd
      { lett = letTok
      , dec = dec
      , inn = inTok
      , exps = Seq.singleton exp
      , delims = Seq.empty ()
      , endd = endTok
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
      { left = openCurlyTok
      , elems = Seq.fromList
          (List.map (fn (a, b) => RecordRow {lab = a, eq = equalTok, exp = b})
             params)
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length params - 1))
      , right = closeCurlyTok
      }

  fun listExp exps =
    List
      { left = openSquareTok
      , elems = Seq.fromList exps
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length exps - 1))
      , right = closeSquareTok
      }

  fun appExp [] = raise Fail "Empty application"
    | appExp [exp] = exp
    | appExp (exp :: exps) =
        List.foldl (fn (e, acc) => App {left = acc, right = e}) exp exps

  fun singleFnExp pat exp =
    Fn
      { fnn = fnTok
      , elems = Seq.singleton {pat = pat, arrow = fatArrowTok, exp = exp}
      , delims = Seq.empty ()
      , optbar = NONE
      }

  fun multFnExp tups =
    Fn
      { fnn = fnTok
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
      { vall = valTok
      , tyvars = SyntaxSeq.Empty
      , elems = Seq.singleton {recc = NONE, pat = pat, eq = equalTok, exp = exp}
      , delims = Seq.empty ()
      }

  fun valDecs _ [] = DecEmpty
    | valDecs recc ((pat, exp) :: t) =
        let
          fun mkRec recc pat exp =
            {recc = recc, pat = pat, eq = equalTok, exp = exp}
        in
          DecVal
            { vall = valTok
            , tyvars = SyntaxSeq.Empty
            , elems = Seq.fromList
                (mkRec (if recc then SOME recTok else NONE) pat exp
                 :: (List.map (fn (pat, exp) => mkRec NONE pat exp) t))
            , delims = Seq.fromList (List.map (fn _ => andReservedTok) t)
            }
        end

  fun multDec decs =
    DecMultiple
      { elems = Seq.fromList decs
      , delims = Seq.fromList (List.map (fn _ => NONE) decs)
      }

  fun singleFunDec tok args exp =
    DecFun
      { funn = funTok
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
      { funn = funTok
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
      { locall = localTok
      , left_dec = dec
      , inn = inTok
      , right_dec = body
      , endd = endTok
      }
  fun localDecs decs body =
    case decs of
      [] => body
    | _ => localDec (multDec decs) body

  val genericDec = DecOpen {openn = openTok, elems = Seq.singleton genericTok}
  val tieDec = DecOpen {openn = openTok, elems = Seq.singleton tieTok}

  fun destructRecordPat patTokens =
    Pat.Record
      { left = openCurlyTok
      , elems = Seq.fromList
          (List.map (fn tok => Pat.LabAsPat {id = tok, ty = NONE, aspat = NONE})
             patTokens)
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length patTokens - 1))
      , right = closeCurlyTok
      }

  fun destructRecordPat' rows =
    Pat.Record
      { left = openCurlyTok
      , elems = Seq.fromList
          (List.map
             (fn (lab, pat) =>
                Pat.LabEqPat {lab = lab, eq = equalTok, pat = pat}) rows)
      , delims = Seq.tabulate (fn _ => commaTok) (Int.max
          (0, List.length rows - 1))
      , right = closeCurlyTok
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
      { left = openSquareTok
      , elems = Seq.fromList pats
      , delims = Seq.fromList
          (case pats of
             [] => []
           | _ :: pats => List.map (fn _ => commaTok) pats)
      , right = closeSquareTok
      }

  fun destructConPat tok pat =
    Pat.Con {opp = NONE, id = MaybeLongToken.make tok, atpat = pat}

  val wildPat = Pat.Wild underTok

  fun parensTy ty =
    Ty.Parens {left = openParenTok, ty = ty, right = closeParenTok}

  fun simpleStructStrDec strid strdec =
    Ast.Str.DecStructure
      { structuree = structureTok
      , elems = Seq.singleton
          { strid = strid
          , constraint = NONE
          , eq = equalTok
          , strexp =
              Ast.Str.Struct
                {structt = structTok, strdec = strdec, endd = endTok}
          }
      , delims = Seq.empty ()
      }

  fun simpleDatatypeDec datbind =
    Ast.Exp.DecDatatype
      {datatypee = datatypeTok, datbind = datbind, withtypee = NONE}

  fun replicateDatatypeDec left right =
    Ast.Exp.DecReplicateDatatype
      { left_datatypee = datatypeTok
      , left_id = left
      , eq = equalTok
      , right_datatypee = datatypeTok
      , right_id = MaybeLongToken.make right
      }

  fun replicateDatatypeToTypbind left right =
    { elems = Seq.singleton
        { tyvars = Ast.SyntaxSeq.Empty
        , tycon = left
        , eq = equalTok
        , ty = Ast.Ty.Con {args = Ast.SyntaxSeq.Empty, id = right}
        }
    , delims = Seq.empty ()
    }
end
