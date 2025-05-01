structure HashGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val mkHash = prependToken "hash"
  val resultTok = mkToken "result"
  val combineTok = mkToken "combine"

  fun combineExpsInLet [] =
        raise Fail "combineExpsInLet: expected non empty list of expressions"
    | combineExpsInLet (head :: rest) =
        let
          val headDec = valDec (identPat resultTok) head
          val restDecs =
            List.map
              (fn exp =>
                 valDec (identPat resultTok) (appExp
                   [Const combineTok, tupleExp [Const resultTok, exp]])) rest
        in
          singleLetExp (multDec (headDec :: restDecs)) (Const resultTok)
        end

  fun tyCon (env as Env {env = env', ...}) v (s: string) (args: Ty.ty list) =
    let
      val atom = Atom.atom s
      val con = Const
        (if tyconIsGeneratedFix env' s then mkToken s else mkHash (mkToken s))
      val constrExp =
        case args of
          [] => con
        | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
    in
      [appExp [constrExp, Const v]]
    end
  and tyExp' env ty =
    let
      val env = Env.freshEnv env
    in
      case (destructTyPat (Env.fresh env) ty, tyExp (envVars env) ty) of
        (Pat.Const _, [App {left, right = Const _, ...}]) => left
      | (pat, [exp]) => singleFnExp pat exp
      | (pat, exps) => singleFnExp pat (combineExpsInLet exps)
    end
  and tyExp (Env {vars = vars as ref (h :: t), ...}) (Ty.Var v) =
        (vars := t; [appExp [Const (mkTyVar v), Const h]])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        List.concat (List.map (tyExp env o #ty) (Seq.toList elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        List.concat (List.map (tyExp env) (Seq.toList elems))
    | tyExp (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val args = syntaxSeqToList args
          fun con v =
            case generatedFixNameForTy env' ty of
              SOME ty => [appExp [Const ty, Const v]]
            | NONE => tyCon env v id args
        in
          case (id, args) of
            ("ref", [ty]) => tyExp env ty
          | ("unit", []) => [Const (mkToken "0wx65B2531B")]
          | _ =>
              (case !vars of
                 h :: t => (vars := t; con h)
               | [] => raise Fail "No vars in con")
        end
    | tyExp _ (Ty.Arrow _) = raise Fail "Cannot hash function"
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp = raise Fail "fuck"

  fun genTypebind ({elems, ...}: typbind) = raise Fail "fuck"

  fun genSimpleDatabind (env, tyTok, vars, Databind constrs) = raise Fail "fuck"
    | genSimpleDatabind (_, tyTok, vars, Typebind ty) = raise Fail "fuck"

  fun genRecursiveDatabind (env, tycons, tys, vars) = raise Fail "fuck"

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
