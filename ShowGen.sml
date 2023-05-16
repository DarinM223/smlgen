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
  fun envVars (Env {vars, ...}) =
    (vars := List.rev (!vars); vars)

  fun mkShow t =
    mkToken ("show" ^ capitalize (Token.toString t))

  val concatTok = mkToken "^"
  val openSquare = stringTok (mkReservedToken OpenSquareBracket)
  val closeSquare = stringTok (mkReservedToken CloseSquareBracket)
  val openParen = stringTok (mkReservedToken OpenParen)
  val closeParen = stringTok (mkReservedToken CloseParen)
  val openCurly = stringTok (mkReservedToken OpenCurlyBracket)
  val closeCurly = stringTok (mkReservedToken CloseCurlyBracket)
  val equalsTok = mkToken " = "
  val commaTok = mkToken ", "
  val concatWithTok = mkToken "String.concatWith"

  fun tyPat env (Ty.Var v) =
        Pat.Const (fresh env (mkTyVar v))
    | tyPat env (Ty.Record {elems, ...}) =
        destructRecordPat' (List.map (fn {lab, ty, ...} => (lab, tyPat env ty))
          (ArraySlice.foldr (op::) [] elems))
    | tyPat env (Ty.Tuple {elems, ...}) =
        destructTuplePat (List.map (tyPat env)
          (ArraySlice.foldr (op::) [] elems))
    | tyPat env (Ty.Con {id, ...}) =
        Pat.Const (fresh env (MaybeLongToken.getToken id))
    | tyPat _ (Ty.Arrow _) = wildPat
    | tyPat env (Ty.Parens {ty, ...}) = tyPat env ty

  fun tyCon _ v "string" [] = Const v
    | tyCon _ v "int" [] =
        appExp [Const (mkToken "Int.toString"), Const v]
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
          val con = Const (mkToken ("show" ^ capitalize s))
          val constrExp =
            case args of
              [] => con
            | args => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          appExp [constrExp, Const v]
        end
  and tyExp' env ty =
    let val env = Env {c = ref 0, vars = ref [], env = env}
    in singleFnExp (tyPat env ty) (tyExp env ty)
    end
  and tyExp (Env {vars = vars as ref (h :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), Const h])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        let
          fun enclose exp =
            Const openCurly :: exp :: [Const closeCurly]
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
          fun enclose exp =
            Const openParen :: exp :: [Const closeParen]
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
          fun con v =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, Const v]
            | NONE => tyCon env v id (syntaxSeqToList args)
        in
          case !vars of
            h :: t => (vars := t; con h)
          | [] => raise Fail "No vars in con"
        end
    | tyExp _ (ty as Ty.Arrow _) =
        Const (stringTok (mkToken (showTy ty)))
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val env = Env {c = ref 0, vars = ref [], env = env}
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             ( conPat id (tyPat env ty)
             , infixLExp concatTok [Const (stringTok id), tyExp env ty]
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
               val env = envWithVars (syntaxSeqToList tyvars) env
               val varsPat = destructTuplePat
                 (List.map (Pat.Const o mkTyVar) (syntaxSeqToList tyvars))
             in
               valDec (Pat.Const (mkShow tycon)) (singleFnExp varsPat
                 (tyExp' env ty))
             end) (ArraySlice.foldr (op::) [] elems)
    in
      multDec decs
    end

  fun genSimpleDatabind (env, ty, vars, constrs) =
    let
      fun header exp =
        case vars of
          [] => exp
        | _ => singleFnExp (destructTuplePat (List.map Pat.Const vars)) exp
    in
      valDec (Pat.Const ty) (header (genConstrs (env, constrs)))
    end

  fun genRecursiveDatabind (env, tycons, tys, vars) = raise Fail ""

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  (* fun genDatabind ({elems, ...}: datbind) =
    let
      val elems = ArraySlice.foldr (op::) [] elems
      val decs =
        List.map
          (fn {tycon, tyvars, elems, ...} =>
             let
               val elems = ArraySlice.foldr (op::) [] elems
               val tyvars =
                 List.map (Pat.Const o mkTyVar) (syntaxSeqToList tyvars)
               fun header exp =
                 case tyvars of
                   [] => exp
                 | _ => singleFnExp (destructTuplePat tyvars) exp
             in
               valDec (Pat.Const (mkShow tycon)) (header (genConstrs elems))
             end) elems
    in
      multDec decs
    end *)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
