structure CompareGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val mkCompare = prependToken "compare"

  val equalCmpTok = mkToken "EQUAL"
  val greaterCmpTok = mkToken "GREATER"
  val lessCmpTok = mkToken "LESS"
  fun caseChain (exp, exps) =
    parensExp (Case
      { casee = caseTok
      , exp = exp
      , off = ofTok
      , elems = Seq.fromList
          [ { pat = Pat.Const equalCmpTok
            , arrow = fatArrowTok
            , exp = caseChainExp exps
            }
          , {pat = Pat.Const quesTok, arrow = fatArrowTok, exp = Const quesTok}
          ]
      , delims = Seq.singleton orTok
      , optbar = NONE
      })
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
      val (someTok, noneTok) = (mkToken "SOME", mkToken "NONE")
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
    , ("String.string", "String.compare")
    , ("String.char", "Char.compare")
    , ("Int.int", "Int.compare")
    , ("Int32.int", "Int32.compare")
    , ("Int63.int", "Int63.compare")
    , ("Int64.int", "Int64.compare")
    , ("LargeInt.int", "LargeInt.compare")
    , ("FixedInt.int", "FixedInt.compare")
    , ("Position.int", "Position.compare")
    , ("IntInf.int", "IntInf.compare")
    , ("Real.real", "Real.compare")
    , ("LargeReal.real", "LargeReal.compare")
    , ("Char.char", "Char.compare")
    , ("Word.word", "Word.compare")
    , ("Word8.word", "Word8.compare")
    , ("Word32.word", "Word32.compare")
    , ("Word64.word", "Word64.compare")
    , ("LargeWord.word", "LargeWord.compare")
    , ("Date.date", "Date.compare")
    , ("CharVectorSlice.slice", "Substring.compare")
    , ("Substring.substring", "Substring.compare")
    , ("WideCharVectorSlice.slice", "WideSubstring.compare")
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
    | tyCon env e "Bool.bool" [] =
        tyCon env e "bool" []
    | tyCon env e "list" [a] =
        ( Env.setOption env ("list", true)
        ; appExp [Const (mkToken "compareList"), parensExp (tyExp' env a), e]
        )
    | tyCon env e "List.list" [a] =
        tyCon env e "list" [a]
    | tyCon env e "option" [a] =
        ( Env.setOption env ("option", true)
        ; appExp [Const (mkToken "compareOption"), parensExp (tyExp' env a), e]
        )
    | tyCon env e "Option.option" [a] =
        tyCon env e "option" [a]
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
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          appExp [constrExp, e]
        end
  and tyExp' env ty =
    let
      val env = Env.freshEnv env
    in
      case (destructTyPatTwice env ty, tyExp env ty) of
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
  and tyExp (Env {vars = vars as ref (a :: b :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), tupleExp [Const a, Const b]])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        caseChainExp (List.map (tyExp env o #ty) (Seq.toList elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        caseChainExp (List.map (tyExp env) (Seq.toList elems))
    | tyExp (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val args = syntaxSeqToList args
          fun con e =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, e]
            | NONE => tyCon env e id args
        in
          case (id, args) of
            ("ref", [ty]) => tyExp env ty
          | ("unit", []) => Const equalCmpTok
          | _ =>
              (case !vars of
                 a :: b :: t => (vars := t; con (tupleExp [Const a, Const b]))
               | _ => raise Fail "No vars in con")
        end
    | tyExp _ (Ty.Arrow _) = raise Fail "Cannot compare functions"
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

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
                        , tyExp env ty
                        )
                      end
                  | NONE =>
                      ( destructTuplePat [Pat.Const id1, Pat.Const id2]
                      , Const equalCmpTok
                      ))) (combinedConstrs constrs)
    in
      multFnExp tups
    end

  fun genTypebind ({elems, ...}: typbind) =
    let
      val env = Env.empty (mkEnv (! Options.defaultTableSize))
      val decs =
        List.map
          (fn {ty, tycon, tyvars, ...} =>
             let
               val vars = syntaxSeqToList tyvars
               val env = Env.setSubEnv (Env.freshEnv env) (envWithVars vars)
               val header =
                 case vars of
                   [] => (fn e => e)
                 | _ =>
                     singleFnExp (destructTuplePat
                       (List.map (Pat.Const o mkTyVar) vars))
             in
               valDec (Pat.Const (mkCompare tycon)) (header (tyExp' env ty))
             end) (Seq.toList elems)
    in
      localDecs (additionalDecs env) (multDec decs)
    end

  fun genSimpleDatabind (env, tyTok, vars, Databind constrs) =
        let
          val env = Env.empty env
          fun header exp =
            case List.map (Pat.Const o mkTyVar) vars of
              [] => exp
            | vars => singleFnExp (destructTuplePat vars) exp
          val dec = valDec (Pat.Const (mkCompare tyTok)) (header
            (genConstrs (env, constrs)))
        in
          localDecs (additionalDecs env) dec
        end
    | genSimpleDatabind (_, tyTok, vars, Typebind ty) =
        genSingleTypebind genTypebind (tyTok, vars, ty)

  fun genRecursiveDatabind (env, tycons, tys, vars) =
    let
      val env as Env {env = env', ...} = Env.empty env
      val varExps = List.map Ty.Var vars
      val dups: IntRedBlackSet.set AtomTable.hash_table =
        AtomTable.mkTable (List.length tycons, LibBase.NotFound)
      val generatorDecs =
        List.map
          (fn (tycon, ty) =>
             let
               val tyconA = Atom.atom (Token.toString tycon)
               val args =
                 List.map
                   (fn Ty.Con {id, ...} => MaybeLongToken.getToken id
                     | Ty.Var v => mkTyVar v
                     | _ => raise Fail "Invalid arg")
                   (generatedArgsForTy env' ty)
               val argDups = findDuplicates args
               val () = AtomTable.insert dups (tyconA, argDups)
               val substMap = buildSubstMap env' (Token.toString tycon) varExps
             in
               ( Pat.Const tycon
               , singleFnExp
                   (destructTuplePat
                      (applyDuplicates (argDups, Pat.Const, args)))
                   (case tyconData env' tyconA of
                      Databind constrs =>
                        genConstrs
                          (env, List.map (substConstr substMap) constrs)
                    | Typebind ty => tyExp' env (subst substMap ty))
               )
             end) (ListPair.zip (tycons, tys))
      val concatTys = mkToken (String.concatWith "_"
        (List.map Token.toString tycons))
      val mutRecDec = valDecs true
        (List.map
           (fn (tycon, args) =>
              let
                val tycon' = baseTyName (Token.toString tycon)
                val argDups = AtomTable.lookup dups (Atom.atom tycon')
                val env = Env.freshEnv env
                val args = applyDuplicates (argDups, tyExp' env, args)
              in
                ( Pat.Const tycon
                , singleFnExp (Pat.Const quesTok) (appExp
                    [Const (mkToken tycon'), tupleExp args, Const quesTok])
                )
              end) (generatedFixesAndArgs env'))
      val tyToks = List.map (Option.valOf o generatedFixNameForTy env') tys
      val dec = multDec
        (additionalDecs env
         @
         [ valDecs true generatorDecs
         , valDec (Pat.Const concatTys)
             (singleFnExp
                (destructTuplePat (List.map (Pat.Const o mkTyVar) vars))
                (singleLetExp mutRecDec (tupleExp (List.map Const tyToks))))
         ])
      val unpacked = unpackingDecs
        (env', vars, concatTys, tycons, mkCompare, "Int.compare")
    in
      localDec dec (multDec unpacked)
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
