structure EqGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  fun genTypebind ({elems, ...}: typbind) = raise Fail "fuck"

  fun genSimpleDatabind (env, tyTok, vars, Databind constrs) = raise Fail "fuck"
    | genSimpleDatabind (_, tyTok, vars, Typebind ty) = raise Fail "fuck"

  fun genRecursiveDatabind (env, tycons, tys, vars) = raise Fail "fuck"

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
