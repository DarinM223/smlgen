structure CompareGen =
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
  val tTok = mkToken "t"

  fun tyPat env (Ty.Var _) =
        Pat.Const (fresh env tTok)
    | tyPat env (Ty.Record {elems, ...}) =
        destructRecordPat' (List.map (fn {lab, ty, ...} => (lab, tyPat env ty))
          (ArraySlice.foldr (op::) [] elems))
    | tyPat env (Ty.Tuple {elems, ...}) =
        destructTuplePat (List.map (tyPat env)
          (ArraySlice.foldr (op::) [] elems))
    | tyPat env (Ty.Con _) =
        Pat.Const (fresh env tTok)
    | tyPat _ (Ty.Arrow _) = wildPat
    | tyPat env (Ty.Parens {ty, ...}) = tyPat env ty
  and tyPat' (env as Env {vars, ...}) ty =
    let
      val pat1 = tyPat env ty
      val vars1 = !vars before vars := []
      val pat2 = tyPat env ty
      val vars2 = !vars
      fun interleave (build, x :: xs, y :: ys) =
            interleave (x :: y :: build, xs, ys)
        | interleave (_, _ :: _, _) = raise Fail "Lists are different sizes"
        | interleave (_, _, _ :: _) = raise Fail "Lists are different sizes"
        | interleave (build, [], []) = build
    in
      (vars := interleave ([], vars1, vars2), destructTuplePat [pat1, pat2])
    end

  fun genTypebind ({elems, ...}: typbind) = raise Fail "typebind"

  fun genSimpleDatabind (env, ty, vars, constrs) = raise Fail "simple databind"
  fun genRecursiveDatabind (env, tycons, tys, vars) =
    raise Fail "recursive databind"

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
