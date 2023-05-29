structure ShowGen =
struct
  open BuildAst Utils MutRecTy

  datatype env = Env of {c: int ref, vars: Token.t list ref, env: MutRecTy.env}
  fun fresh (Env {c, vars, ...}) t =
    let
      val i = !c before c := !c + 1
      val tok = appendTokens t (mkToken (Int.toString i))
    in
      (vars := tok :: !vars; tok)
    end
  fun envVars (env as Env {vars, ...}) =
    (vars := List.rev (!vars); env)
  val mkShow = prependToken "show"

  val concatTok = mkToken "^"
  val openSquare = stringTok (mkReservedToken OpenSquareBracket)
  val closeSquare = stringTok (mkReservedToken CloseSquareBracket)
  val openParen = stringTok (mkReservedToken OpenParen)
  val closeParen = stringTok (mkReservedToken CloseParen)
  val openCurly = stringTok (mkReservedToken OpenCurlyBracket)
  val closeCurly = stringTok (mkReservedToken CloseCurlyBracket)
  val quotTok = stringTok (mkToken "\\\"")
  val strSpaceTok = mkToken "\" \""
  val equalsTok = mkToken " = "
  val commaTok = mkToken ", "
  val concatWithTok = mkToken "String.concatWith"

  fun tyCon _ v "string" [] =
        infixLExp concatTok [Const quotTok, Const v, Const quotTok]
    | tyCon _ v "int" [] =
        appExp [Const (mkToken "Int.toString"), Const v]
    | tyCon _ v "real" [] =
        appExp [Const (mkToken "Real.toString"), Const v]
    | tyCon _ v "char" [] =
        infixLExp concatTok
          [ Const (mkToken "\"#\\\"\"")
          , appExp [Const (mkToken "Char.toString"), Const v]
          , Const (mkToken "\"\\\"\"")
          ]
    | tyCon _ v "bool" [] =
        appExp [Const (mkToken "Bool.toString"), Const v]
    | tyCon (Env {env, ...}) v "list" [a] =
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
    | tyCon (Env {env, ...}) v (s: string) (args: Ty.ty list) =
        let
          val con = Const
            (if tyconIsGeneratedFix env s then mkToken s else mkShow (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          appExp [constrExp, Const v]
        end
  and tyExp' env ty =
    let
      val env = Env {c = ref 0, vars = ref [], env = env}
    in
      case (destructTyPat (fresh env) ty, tyExp (envVars env) ty) of
        (Pat.Const _, App {left, right = Const _, ...}) => left
      | (pat, exp) => singleFnExp pat exp
    end
  and tyExp (Env {vars = vars as ref (h :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), Const h])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        let
          val enclose = fn exp => Const openCurly :: exp :: [Const closeCurly]
          val elems = ArraySlice.foldr (op::) [] elems
          val fields =
            List.map
              (fn {lab, ty, ...} =>
                 infixLExp concatTok
                   [ Const (stringTok (appendTokens lab equalsTok))
                   , tyExp env ty
                   ]) elems
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp env (Ty.Tuple {elems, ...}) =
        let
          val enclose = fn exp => Const openParen :: exp :: [Const closeParen]
          val elems = ArraySlice.foldr (op::) [] elems
          val fields = List.map (tyExp env) elems
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
              infixLExp concatTok
                [ Const (stringTok (mkToken "ref"))
                , Const strSpaceTok
                , tyExp env ty
                ]
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
      val tyToStr = fn a => fn b => Const strSpaceTok :: tyToStr a b
      val env = Env {c = ref 0, vars = ref [], env = env}
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             ( conPat id (destructTyPat (fresh env) ty)
             , infixLExp concatTok
                 (Const (stringTok id) :: tyToStr ty (tyExp (envVars env) ty))
             )
            | {id, ...} => (Pat.Const id, Const (stringTok id))) constrs
    in
      multFnExp tups
    end

  fun genTypebind ({elems, ...}: typbind) =
    let
      val env = mkEnv ()
      val decs =
        List.map
          (fn {ty, tycon, tyvars, ...} =>
             let
               val vars = syntaxSeqToList tyvars
               val env = envWithVars vars env
               val header =
                 case vars of
                   [] => (fn e => e)
                 | _ =>
                     singleFnExp (destructTuplePat
                       (List.map (Pat.Const o mkTyVar) vars))
             in
               valDec (Pat.Const (mkShow tycon)) (header (tyExp' env ty))
             end) (ArraySlice.foldr (op::) [] elems)
    in
      multDec decs
    end

  fun genSimpleDatabind (env, ty, vars, constrs) =
    let
      fun header exp =
        case List.map (Pat.Const o mkTyVar) vars of
          [] => exp
        | vars => singleFnExp (destructTuplePat vars) exp
    in
      valDec (Pat.Const (mkShow ty)) (header (genConstrs (env, constrs)))
    end

  fun genRecursiveDatabind (env, tycons, tys, vars) =
    let
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
                   (generatedArgsForTy env ty)
               val argDups = findDuplicates args
               val () = AtomTable.insert dups (tyconA, argDups)
               val substMap = buildSubstMap env (Token.toString tycon) varExps
               val constrs = List.map (substConstr substMap)
                 (tyconConstrs env tyconA)
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
                val args = applyDuplicates (argDups, tyExp' env, args)
              in
                ( true
                , Pat.Const tycon
                , singleFnExp (Pat.Const quesTok) (appExp
                    [Const (mkToken tycon'), tupleExp args, Const quesTok])
                )
              end) (generatedFixesAndArgs env))
      val tyToks = List.map (Option.valOf o generatedFixNameForTy env) tys
      val dec = multDec
        [ valDecs generatorDecs
        , valDec (Pat.Const concatTys)
            (singleFnExp
               (destructTuplePat (List.map (Pat.Const o mkTyVar) vars))
               (singleLetExp mutRecDec (tupleExp (List.map Const tyToks))))
        ]
    in
      localDec dec (multDec (unpackingDecs
        (concatTys, (List.map mkShow tycons))))
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
