structure CompareGen =
struct
  open BuildAst Utils MutRecTy

  datatype env =
    Env of
      { c: int ref
      , vars: Token.t list ref
      , usesList: bool ref
      , usesBool: bool ref
      , env: MutRecTy.env
      }
  fun emptyEnv env =
    Env
      { c = ref 0
      , vars = ref []
      , usesList = ref false
      , usesBool = ref false
      , env = env
      }
  fun updateEnv (Env r) =
    let
      fun from c vars usesList usesBool env =
        { c = c
        , vars = vars
        , usesList = usesList
        , usesBool = usesBool
        , env = env
        }
      fun to fn__ {c, vars, usesList, usesBool, env} =
        fn__ c vars usesList usesBool env
    in
      FunctionalRecordUpdate.makeUpdate5 (from, from, to) r
    end
  fun freshEnv env =
    let open FunctionalRecordUpdate
    in Env (updateEnv env set #c (ref 0) set #vars (ref []) $)
    end

  fun fresh (Env {c, vars, ...}) t =
    let
      val i = !c before c := !c + 1
      val tok = appendTokens t (mkToken (Int.toString i))
    in
      (vars := tok :: !vars; tok)
    end
  val mkCompare = prependToken "compare"

  fun tyPat (env as Env {vars, ...}) ty =
    let
      val pat1 = destructTyPat (fresh env) ty
      val vars1 = !vars before vars := []
      val pat2 = destructTyPat (fresh env) ty
      val vars2 = !vars
      fun interleave (build, x :: xs, y :: ys) =
            interleave (x :: y :: build, xs, ys)
        | interleave (_, _ :: _, _) = raise Fail "Lists are different sizes"
        | interleave (_, _, _ :: _) = raise Fail "Lists are different sizes"
        | interleave (build, [], []) = build
    in
      (vars := interleave ([], vars1, vars2); (pat1, pat2))
    end

  val caseTok = mkReservedToken Token.Case
  val ofTok = mkReservedToken Of
  val equalCmpTok = mkToken "EQUAL"
  val greaterCmpTok = mkToken "GREATER"
  val lessCmpTok = mkToken "LESS"
  fun caseChainExp [] = raise Fail "Empty case chain"
    | caseChainExp [exp] = exp
    | caseChainExp (exp :: exps) =
        parensExp (Case
          { casee = caseTok
          , exp = exp
          , off = ofTok
          , elems = ArraySlice.full (Array.fromList
              [ { pat = Pat.Const equalCmpTok
                , arrow = fatArrowTok
                , exp = caseChainExp exps
                }
              , { pat = Pat.Const quesTok
                , arrow = fatArrowTok
                , exp = Const quesTok
                }
              ])
          , delims = ArraySlice.full (Array.fromList [orTok])
          , optbar = NONE
          })
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
  fun additionalDecs (Env {usesList, usesBool, ...}) =
    let
      fun addCompareList a =
        if !usesList then compareListDec :: a else a
      fun addCompareBool a =
        if !usesBool then compareBoolDec :: a else a
    in
      (addCompareBool o addCompareList) []
    end

  fun tyCon _ e "string" [] =
        appExp [Const (mkToken "String.compare"), e]
    | tyCon _ e "int" [] =
        appExp [Const (mkToken "Int.compare"), e]
    | tyCon _ e "real" [] =
        appExp [Const (mkToken "Real.compare"), e]
    | tyCon _ e "char" [] =
        appExp [Const (mkToken "Char.compare"), e]
    | tyCon (Env {usesBool, ...}) e "bool" [] =
        (usesBool := true; appExp [Const (mkToken "compareBool"), e])
    | tyCon (env as Env {usesList, ...}) e "list" [a] =
        ( usesList := true
        ; appExp [Const (mkToken "compareList"), parensExp (tyExp' env a), e]
        )
    | tyCon (env as Env {env = env', ...}) e (s: string) (args: Ty.ty list) =
        let
          val con = Const
            (if tyconIsGeneratedFix env' s then mkToken s
             else mkCompare (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          appExp [constrExp, e]
        end
  and tyExp' env ty =
    let
      val env = freshEnv env
    in
      case (tyPat env ty, tyExp env ty) of
        ( (pat1 as Pat.Const a, pat2 as Pat.Const b)
        , exp as App {left, right = Tuple {elems, ...}, ...}
        ) =>
          (case ArraySlice.foldr (op::) [] elems of
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
        caseChainExp (List.map (tyExp env o #ty)
          (ArraySlice.foldr (op::) [] elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        caseChainExp (List.map (tyExp env) (ArraySlice.foldr (op::) [] elems))
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
      val env = freshEnv env
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
                        val (pat1, pat2) = tyPat env ty
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
      val env = emptyEnv (mkEnv ())
      val decs =
        List.map
          (fn {ty, tycon, tyvars, ...} =>
             let
               val vars = syntaxSeqToList tyvars
               open FunctionalRecordUpdate
               val env = Env
                 (updateEnv (freshEnv env) upd #env (envWithVars vars) $)
               val header =
                 case vars of
                   [] => (fn e => e)
                 | _ =>
                     singleFnExp (destructTuplePat
                       (List.map (Pat.Const o mkTyVar) vars))
             in
               valDec (Pat.Const (mkCompare tycon)) (header (tyExp' env ty))
             end) (ArraySlice.foldr (op::) [] elems)
    in
      case additionalDecs env of
        [] => multDec decs
      | decs' => localDec (multDec decs') (multDec decs)
    end

  fun genSimpleDatabind (env, ty, vars, constrs) =
    let
      val env = emptyEnv env
      fun header exp =
        case List.map (Pat.Const o mkTyVar) vars of
          [] => exp
        | vars => singleFnExp (destructTuplePat vars) exp
      val dec = valDec (Pat.Const (mkCompare ty)) (header
        (genConstrs (env, constrs)))
    in
      case additionalDecs env of
        [] => dec
      | decs' => localDec (multDec decs') dec
    end

  fun genRecursiveDatabind (env, tycons, tys, vars) =
    let
      val env as Env {env = env', ...} = emptyEnv env
      val varExps = List.map Ty.Var vars
      val dups: IntRedBlackSet.set AtomTable.hash_table =
        AtomTable.mkTable (100, LibBase.NotFound)
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
               val constrs = List.map (substConstr substMap)
                 (tyconConstrs env' tyconA)
             in
               ( true
               , Pat.Const tycon
               , singleFnExp
                   (destructTuplePat
                      (applyDuplicates (argDups, Pat.Const, args)))
                   (genConstrs (env, constrs))
               )
             end) (ListPair.zip (tycons, tys))
      val concatTys = mkToken (String.concatWith "_"
        (List.map Token.toString tycons))
      val mutRecDec = valDecs
        (List.map
           (fn (tycon, args) =>
              let
                val tycon' = baseTyName (Token.toString tycon)
                val argDups = AtomTable.lookup dups (Atom.atom tycon')
                val env = freshEnv env
                val args = applyDuplicates (argDups, tyExp' env, args)
              in
                ( true
                , Pat.Const tycon
                , singleFnExp (Pat.Const quesTok) (appExp
                    [Const (mkToken tycon'), tupleExp args, Const quesTok])
                )
              end) (generatedFixesAndArgs env'))
      val tyToks = List.map (Option.valOf o generatedFixNameForTy env') tys
      val dec = multDec
        (additionalDecs env
         @
         [ valDecs generatorDecs
         , valDec (Pat.Const concatTys)
             (singleFnExp
                (destructTuplePat (List.map (Pat.Const o mkTyVar) vars))
                (singleLetExp mutRecDec (tupleExp (List.map Const tyToks))))
         ])
    in
      localDec dec (multDec (unpackingDecs
        (concatTys, (List.map mkCompare tycons))))
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
