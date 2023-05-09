structure ShowGen =
struct
  open BuildAst Utils

  datatype env = Env of {c: int ref, vars: Token.t list ref}
  fun fresh (Env {c, vars}) t =
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

  fun tyExp (vars as ref (h :: t)) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), Const h])
    | tyExp _ (Ty.Var v) =
        raise Fail ("Empty vars list at var: " ^ Token.toString v)
    | tyExp vars (Ty.Record {elems, ...}) =
        let
          fun enclose exp =
            Const openCurly :: exp :: [Const closeCurly]
          val elems = ArraySlice.foldr (op::) [] elems
          val fields =
            List.map
              (fn {lab, ty, ...} =>
                 infixLExp concatTok
                   [ Const (stringTok (appendTokens lab equalsTok))
                   , tyExp vars ty
                   ]) elems
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp vars (Ty.Tuple {elems, ...}) =
        let
          fun enclose exp =
            Const openParen :: exp :: [Const closeParen]
          val elems = ArraySlice.foldr (op::) [] elems
          val fields = List.map (tyExp vars) elems
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp (vars as ref (h :: t)) (Ty.Con {id, ...}) =
        ( vars := t
        ; appExp [Const (mkShow (MaybeLongToken.getToken id)), Const h]
        )
    | tyExp _ (Ty.Con {id, ...}) =
        raise Fail
          ("Empty vars list at con: "
           ^ Token.toString (MaybeLongToken.getToken id))
    | tyExp _ (ty as Ty.Arrow _) =
        Const (stringTok (mkToken (showTy ty)))
    | tyExp vars (Ty.Parens {ty, ...}) = tyExp vars ty

  fun genConstrs (constrs: constr list) : Exp.exp =
    let
      val env = Env {c = ref 0, vars = ref []}
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             ( conPat id (tyPat env ty)
             , infixLExp concatTok
                 [Const (stringTok id), tyExp (envVars env) ty]
             )
            | {id, ...} => (Pat.Const id, Const (stringTok id))) constrs
    in
      multFnExp tups
    end

  fun genTypebind ({elems, ...}: typbind) =
    let
      val env = Env {c = ref 0, vars = ref []}
      val decs =
        List.map
          (fn {ty, tycon, tyvars, ...} =>
             let
               val varsPat = destructTuplePat
                 (List.map (Pat.Const o mkTyVar) (syntaxSeqToList tyvars))
             in
               valDec (Pat.Const (mkShow tycon))
                 (singleFnExp varsPat (singleFnExp (tyPat env ty)
                    (tyExp (envVars env) ty)))
             end) (ArraySlice.foldr (op::) [] elems)
    in
      multDec decs
    end

  fun genDatabind ({elems, ...}: datbind) =
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
    end

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
