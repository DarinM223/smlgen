structure CompareGenBuild =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val mkCompare = prependToken "compare"
  val prefixGen = mkCompare
  val defaultGenFnName = "Int.compare"

  val equalCmpTok = mkToken "EQUAL"
  val greaterCmpTok = mkToken "GREATER"
  val lessCmpTok = mkToken "LESS"
  fun caseChain (exp, exps) =
    parensExp (caseExp exp
      [ (Pat.Const equalCmpTok, caseChainExp exps)
      , (Pat.Const quesTok, Const quesTok)
      ])
  and caseChainExp [] = raise Fail "Empty case chain"
    | caseChainExp [exp] = exp
    | caseChainExp (exp :: (exps as Const tok :: exps')) =
        if Token.same (tok, equalCmpTok) then caseChainExp (exp :: exps')
        else caseChain (exp, exps)
    | caseChainExp (exp :: exps) = caseChain (exp, exps)
  val compareBoolDec =
    let
      val conTok = mkToken "compareBool"
    in
      multFunDec
        [[ ( conTok
           , [destructTuplePat [Pat.Const falseTok, Pat.Const trueTok]]
           , Const lessCmpTok
           )
         , ( conTok
           , [destructTuplePat [Pat.Const trueTok, Pat.Const falseTok]]
           , Const greaterCmpTok
           )
         , (conTok, [destructTuplePat [wildPat, wildPat]], Const equalCmpTok)
         ]]
    end
  val compareOptionDec =
    let
      val conTok = mkToken "compareOption"
      val cmpTok = mkToken "cmp"
      val (xTok, yTok) = (mkToken "x", mkToken "y")
    in
      multFunDec
        [[ ( conTok
           , [ Pat.Const cmpTok
             , destructTuplePat
                 [ destructConPat someTok (Pat.Const xTok)
                 , destructConPat someTok (Pat.Const yTok)
                 ]
             ]
           , appExp [Const cmpTok, tupleExp [Const xTok, Const yTok]]
           )
         , ( conTok
           , [ wildPat
             , destructTuplePat
                 [destructConPat someTok wildPat, Pat.Const noneTok]
             ]
           , Const greaterCmpTok
           )
         , ( conTok
           , [ wildPat
             , destructTuplePat
                 [Pat.Const noneTok, destructConPat someTok wildPat]
             ]
           , Const lessCmpTok
           )
         , ( conTok
           , [wildPat, destructTuplePat [Pat.Const noneTok, Pat.Const noneTok]]
           , Const equalCmpTok
           )
         ]]
    end
  val compareListDec =
    let
      val conTok = mkToken "compareList"
      val cmpTok = mkToken "cmp"
      val (xTok, xsTok) = (mkToken "x", mkToken "xs")
      val (yTok, ysTok) = (mkToken "y", mkToken "ys")
      val consTok = mkToken "::"
    in
      multFunDec
        [[ ( conTok
           , [ Pat.Const cmpTok
             , destructTuplePat
                 [ destructInfixLPat consTok [Pat.Const xTok, Pat.Const xsTok]
                 , destructInfixLPat consTok [Pat.Const yTok, Pat.Const ysTok]
                 ]
             ]
           , caseChainExp
               [ appExp [Const cmpTok, tupleExp [Const xTok, Const yTok]]
               , appExp
                   [ Const conTok
                   , Const cmpTok
                   , tupleExp [Const xsTok, Const ysTok]
                   ]
               ]
           )
         , ( conTok
           , [ wildPat
             , destructTuplePat
                 [ destructInfixLPat consTok [wildPat, wildPat]
                 , destructListPat []
                 ]
             ]
           , Const greaterCmpTok
           )
         , ( conTok
           , [ wildPat
             , destructTuplePat
                 [ destructListPat []
                 , destructInfixLPat consTok [wildPat, wildPat]
                 ]
             ]
           , Const lessCmpTok
           )
         , (conTok, [wildPat, wildPat], Const equalCmpTok)
         ]]
    end
  fun additionalDecs env =
    let
      fun addCompareOption a =
        if Env.getOption env "option" then compareOptionDec :: a else a
      fun addCompareList a =
        if Env.getOption env "list" then compareListDec :: a else a
      fun addCompareBool a =
        if Env.getOption env "bool" then compareBoolDec :: a else a
    in
      (addCompareBool o addCompareList o addCompareOption) []
    end

  val rewrites =
    [ ("string", "String.compare")
    , ("int", "Int.compare")
    , ("real", "Real.compare")
    , ("char", "Char.compare")
    , ("word", "Word.compare")
    , ("Int32.int", "Int32.compare")
    , ("Int63.int", "Int63.compare")
    , ("Int64.int", "Int64.compare")
    , ("LargeInt.int", "LargeInt.compare")
    , ("FixedInt.int", "FixedInt.compare")
    , ("Position.int", "Position.compare")
    , ("IntInf.int", "IntInf.compare")
    , ("LargeReal.real", "LargeReal.compare")
    , ("Char.char", "Char.compare")
    , ("Word8.word", "Word8.compare")
    , ("Word32.word", "Word32.compare")
    , ("Word63.word", "Word63.compare")
    , ("Word64.word", "Word64.compare")
    , ("LargeWord.word", "LargeWord.compare")
    , ("Date.date", "Date.compare")
    , ("Substring.substring", "Substring.compare")
    , ("WideSubstring.substring", "WideSubstring.compare")
    , ("Time.time", "Time.compare")
    ]
  val rewriteMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty rewrites

  fun tyCon env e "bool" [] =
        ( Env.setOption env ("bool", true)
        ; appExp [Const (mkToken "compareBool"), e]
        )
    | tyCon env e "list" [a] =
        ( Env.setOption env ("list", true)
        ; appExp [Const (mkToken "compareList"), parensExp (tyExp env a), e]
        )
    | tyCon env e "option" [a] =
        ( Env.setOption env ("option", true)
        ; appExp [Const (mkToken "compareOption"), parensExp (tyExp env a), e]
        )
    | tyCon (env as Env {env = env', ...}) e (s: string) (args: Ty.ty list) =
        let
          val atom = Atom.atom s
          val con = Const
            (if tyconIsGeneratedFix env' s then
               mkToken s
             else if AtomRedBlackMap.inDomain (rewriteMap, atom) then
               mkToken (AtomRedBlackMap.lookup (rewriteMap, atom))
             else
               mkCompare (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp env) args)]
        in
          appExp [constrExp, e]
        end
  and tyExp env ty =
    let
      val env = Env.freshEnv env
    in
      case (destructTyPatTwice env ty, tyExp_ env ty) of
        ( (pat1 as Pat.Const a, pat2 as Pat.Const b)
        , exp as App {left, right = Tuple {elems, ...}, ...}
        ) =>
          (case Seq.toList elems of
             [Const a', Const b'] =>
               if Token.same (a, a') andalso Token.same (b, b') then left
               else singleFnExp (destructTuplePat [pat1, pat2]) exp
           | _ => singleFnExp (destructTuplePat [pat1, pat2]) exp)
      | ((pat1, pat2), exp) => singleFnExp (destructTuplePat [pat1, pat2]) exp
    end
  and tyExp_ (Env {vars = vars as ref (a :: b :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), tupleExp [Const a, Const b]])
    | tyExp_ _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp_ env (Ty.Record {elems, ...}) =
        caseChainExp (List.map (tyExp_ env o #ty) (Seq.toList elems))
    | tyExp_ env (Ty.Tuple {elems, ...}) =
        caseChainExp (List.map (tyExp_ env) (Seq.toList elems))
    | tyExp_ (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val id = Option.getOpt (rewriteAlias (Atom.atom id), id)
          val args = syntaxSeqToList args
          fun con e =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, e]
            | NONE => tyCon env e id args
        in
          case (id, args) of
            ("ref", [ty]) => tyExp_ env ty
          | ("unit", []) => Const equalCmpTok
          | _ =>
              (case !vars of
                 a :: b :: t => (vars := t; con (tupleExp [Const a, Const b]))
               | _ => raise Fail "No vars in con")
        end
    | tyExp_ _ (Ty.Arrow _) = Const equalCmpTok
    | tyExp_ env (Ty.Parens {ty, ...}) = tyExp_ env ty

  fun combinedConstrs l =
    let val l = ListPair.zip (l, List.tabulate (List.length l, fn i => i))
    in List.concat (List.map (fn c => List.map (fn c' => (c, c')) l) l)
    end

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val env = Env.freshEnv env
      fun conPat' id (SOME _) = conPat id wildPat
        | conPat' id NONE = Pat.Const id
      val tups =
        List.map
          (fn ( ({arg = arg1, id = id1, ...}, prec1)
              , ({arg = arg2, id = id2, ...}, prec2)
              ) =>
             (case Int.compare (prec1, prec2) of
                GREATER =>
                  ( destructTuplePat [conPat' id1 arg1, conPat' id2 arg2]
                  , Const greaterCmpTok
                  )
              | LESS =>
                  ( destructTuplePat [conPat' id1 arg1, conPat' id2 arg2]
                  , Const lessCmpTok
                  )
              | EQUAL =>
                  case arg1 of
                    SOME {ty, ...} =>
                      let
                        val (pat1, pat2) = destructTyPatTwice env ty
                      in
                        ( destructTuplePat [conPat id1 pat1, conPat id2 pat2]
                        , tyExp_ env ty
                        )
                      end
                  | NONE =>
                      ( destructTuplePat [Pat.Const id1, Pat.Const id2]
                      , Const equalCmpTok
                      ))) (combinedConstrs constrs)
    in
      multFnExp tups
    end
end

structure CompareGen = BasicGeneratorFn(CompareGenBuild)
