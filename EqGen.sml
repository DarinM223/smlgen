structure EqGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val andalsoChainExp = infixLExp andalsoTok

  fun tyCon (env as Env {env = env', ...}) e (s: string) (args: Ty.ty list) =
    raise Fail "fuck"
  and tyExp' env ty =
    let
      val env = Env.freshEnv env
    in
      case (Env.destructTyPatTwice env ty, tyExp env ty) of
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
        andalsoChainExp (List.map (tyExp env o #ty) (Seq.toList elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        andalsoChainExp (List.map (tyExp env) (Seq.toList elems))
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
          | ("unit", []) => Const trueTok
          | _ =>
              (case !vars of
                 a :: b :: t => (vars := t; con (tupleExp [Const a, Const b]))
               | _ => raise Fail "No vars in con")
        end
    | tyExp _ (Ty.Arrow _) = raise Fail "Functions cannot be equal"
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genTypebind ({elems, ...}: typbind) = raise Fail "fuck"

  fun genSimpleDatabind (env, tyTok, vars, Databind constrs) = raise Fail "fuck"
    | genSimpleDatabind (_, tyTok, vars, Typebind ty) = raise Fail "fuck"

  fun genRecursiveDatabind (env, tycons, tys, vars) = raise Fail "fuck"

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
