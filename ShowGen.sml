structure ShowGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  fun envVars (env as Env {vars, ...}) =
    (vars := List.rev (!vars); env)
  val mkShow = prependToken "show"

  val concatTok = mkToken "^"
  val openSquare = stringTok openSquareTok
  val closeSquare = stringTok closeSquareTok
  val openParen = stringTok openParenTok
  val closeParen = stringTok closeParenTok
  val openCurly = stringTok openCurlyTok
  val closeCurly = stringTok closeCurlyTok
  val quotTok = stringTok (mkToken "\\\"")
  val equalsTok = mkToken " = "
  val commaTok = mkToken ", "
  val concatWithTok = mkToken "String.concatWith"
  val unitTok = stringTok (mkToken "()")

  val showOptionDec =
    let
      val conTok = mkToken "showOption"
      val (fTok, sTok) = (mkToken "f", mkToken "s")
      val (someTok, noneTok) = (mkToken "SOME", mkToken "NONE")
    in
      multFunDec
        [[ ( conTok
           , [ Pat.Const fTok
             , parensPat (destructConPat someTok (Pat.Const sTok))
             ]
           , infixLExp concatTok
               [Const (stringTokSpace someTok), appExp [Const fTok, Const sTok]]
           )
         , (conTok, [wildPat, Pat.Const noneTok], Const (stringTok noneTok))
         ]]
    end

  fun additionalDecs env =
    if Env.getOption env "option" then [showOptionDec] else []

  val rewrites =
    [ ("int", "Int.toString")
    , ("real", "Real.toString")
    , ("word", "Word.toString")
    , ("bool", "Bool.toString")
    , ("Int.int", "Int.toString")
    , ("Int32.int", "Int32.toString")
    , ("Int63.int", "Int63.toString")
    , ("Int64.int", "Int64.toString")
    , ("LargeInt.int", "LargeInt.toString")
    , ("FixedInt.int", "FixedInt.toString")
    , ("Position.int", "Position.toString")
    , ("IntInf.int", "IntInf.toString")
    , ("Real.real", "Real.toString")
    , ("Math.real", "Real.toString")
    , ("LargeReal.real", "LargeReal.toString")
    , ("Word.word", "Word.toString")
    , ("Word8.word", "Word8.toString")
    , ("Word32.word", "Word32.toString")
    , ("Word63.word", "Word63.toString")
    , ("Word64.word", "Word64.toString")
    , ("LargeWord.word", "LargeWord.toString")
    , ("Bool.bool", "Bool.toString")
    , ("Date.date", "Date.toString")
    , ("CharVectorSlice.slice", "Substring.string")
    , ("Substring.substring", "Substring.string")
    , ("WideCharVectorSlice.slice", "WideSubstring.string")
    , ("WideSubstring.substring", "WideSubstring.string")
    , ("Time.time", "Time.toString")
    , ("IEEEReal.decimal_approx", "IEEEReal.toString")
    ]
  val rewriteMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty rewrites

  fun tyCon _ v "string" [] =
        infixLExp concatTok [Const quotTok, Const v, Const quotTok]
    | tyCon e v "String.string" [] =
        tyCon e v "string" []
    | tyCon _ v "char" [] =
        infixLExp concatTok
          [ Const (mkToken "\"#\\\"\"")
          , appExp [Const (mkToken "Char.toString"), Const v]
          , Const (mkToken "\"\\\"\"")
          ]
    | tyCon e v "Char.char" [] =
        tyCon e v "char" []
    | tyCon e v "String.char" [] =
        tyCon e v "char" []
    | tyCon env v "list" [a] =
        infixLExp concatTok
          [ Const openSquare
          , appExp
              [ Const concatWithTok
              , Const (stringTok commaTok)
              , parensExp (appExp
                  [ Const (mkToken "List.map")
                  , parensExp (tyExp' env a)
                  , Const v
                  ])
              ]
          , Const closeSquare
          ]
    | tyCon env v "List.list" [a] =
        tyCon env v "list" [a]
    | tyCon env v "option" [a] =
        ( Env.setOption env ("option", true)
        ; appExp
            [Const (mkToken "showOption"), parensExp (tyExp' env a), Const v]
        )
    | tyCon env v "Option.option" [a] =
        tyCon env v "option" [a]
    | tyCon (env as Env {env = env', ...}) v (s: string) (args: Ty.ty list) =
        let
          val atom = Atom.atom s
          val con = Const
            (if tyconIsGeneratedFix env' s then
               mkToken s
             else if AtomRedBlackMap.inDomain (rewriteMap, atom) then
               mkToken (AtomRedBlackMap.lookup (rewriteMap, atom))
             else
               mkShow (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          appExp [constrExp, Const v]
        end
  and tyExp' env ty =
    let
      val env = Env.freshEnv env
    in
      case (destructTyPat (Env.fresh env) ty, tyExp (envVars env) ty) of
        (Pat.Const _, App {left, right = Const _, ...}) => left
      | (pat, exp) => singleFnExp pat exp
    end
  and tyExp (Env {vars = vars as ref (h :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), Const h])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        let
          val enclose = fn exp => Const openCurly :: exp :: [Const closeCurly]
          val fields =
            List.map
              (fn {lab, ty, ...} =>
                 infixLExp concatTok
                   [ Const (stringTok (appendTokens lab equalsTok))
                   , tyExp env ty
                   ]) (Seq.toList elems)
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp env (Ty.Tuple {elems, ...}) =
        let
          val enclose = fn exp => Const openParen :: exp :: [Const closeParen]
          val fields = List.map (tyExp env) (Seq.toList elems)
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val args = syntaxSeqToList args
          fun con v =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, Const v]
            | NONE => tyCon env v id args
        in
          case (id, args) of
            ("ref", [ty]) =>
              infixLExp concatTok [Const (mkToken "\"ref \""), tyExp env ty]
          | ("unit", []) => Const unitTok
          | _ =>
              (case !vars of
                 h :: t => (vars := t; con h)
               | [] => raise Fail "No vars in con")
        end
    | tyExp _ (ty as Ty.Arrow _) =
        Const (stringTok (mkToken (showTy ty)))
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val enclose = fn exp => Const openParen :: exp :: [Const closeParen]
      fun tyToStr (Ty.Con _) = enclose
        | tyToStr _ = fn a => [a]
      val toStr = fn t => mkToken ("\"" ^ Token.toString (stripToken t) ^ " \"")
      val env = Env.freshEnv env
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             ( conPat id (destructTyPat (Env.fresh env) ty)
             , infixLExp concatTok
                 (Const (toStr id) :: tyToStr ty (tyExp (envVars env) ty))
             )
            | {id, ...} => (Pat.Const id, Const (stringTok id))) constrs
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
             in
               valDec (Pat.Const (mkShow tycon)) (header vars (tyExp' env ty))
             end) (Seq.toList elems)
    in
      localDecs (additionalDecs env) (multDec decs)
    end

  fun genSimpleDatabind (env, ty, vars, Databind constrs) =
        let
          val env = Env.empty env
          val dec = valDec (Pat.Const (mkShow ty)) (header vars
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
        (env', vars, concatTys, tycons, mkShow, "Int.toString")
    in
      localDec dec (multDec unpacked)
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
