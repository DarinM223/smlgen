structure Env =
struct
  datatype t =
    Env of
      { c: int ref
      , vars: Token.t list ref
      , options: bool AtomTable.hash_table
      , env: MutRecTy.env
      }
  val optionsSize = 20
  fun empty env =
    Env
      { c = ref 0
      , vars = ref []
      , options = AtomTable.mkTable (optionsSize, LibBase.NotFound)
      , env = env
      }
  fun updateT r =
    let
      fun from c vars options env =
        {c = c, vars = vars, options = options, env = env}
      fun to ? {c, vars, options, env} =
        ?c vars options env
    in
      FunctionalRecordUpdate.makeUpdate4 (from, from, to) r
    end
  fun setSubEnv (Env env) env' =
    let open Fold FunctionalRecordUpdate
    in Env (updateT env upd #env env' $)
    end
  fun freshEnv (Env env) =
    let open Fold FunctionalRecordUpdate
    in Env (updateT env set #c (ref 0) set #vars (ref []) $)
    end
  fun fresh (Env {c, vars, ...}) t =
    let
      val i = !c before c := !c + 1
      val tok = TokenUtils.appendTokens t (TokenUtils.mkToken (Int.toString i))
    in
      (vars := tok :: !vars; tok)
    end
  fun setOption (Env {options, ...}) (opt, flag) =
    AtomTable.insert options (Atom.atom opt, flag)
  fun getOption (Env {options, ...}) opt =
    AtomTable.lookup options (Atom.atom opt)
    handle LibBase.NotFound => false

  (* Given a type, return two pattern deconstructions for that type,
     with the collected variables interleaved between the two patterns.
     For example, if destructTyPat collects variables var1, var2, var3, etc
     then destructTyPatTwice gives two patterns p1 and p2 and collects
     variables p1_var1, p2_var1, p1_var2, p2_var2, p1_var3, p2_var3.
  *)
  fun destructTyPatTwice' destructPat (env as Env {vars, ...}) ty =
    let
      val pat1 = destructPat (fresh env) ty
      val vars1 = !vars before vars := []
      val pat2 = destructPat (fresh env) ty
      val vars2 = !vars
      fun interleave (build, x :: xs, y :: ys) =
            interleave (x :: y :: build, xs, ys)
        | interleave (_, _ :: _, _) = raise Fail "Lists are different sizes"
        | interleave (_, _, _ :: _) = raise Fail "Lists are different sizes"
        | interleave (build, [], []) = build
    in
      (vars := interleave ([], vars1, vars2); (pat1, pat2))
    end
  val destructTyPatTwice = destructTyPatTwice' Utils.destructTyPat
  val destructTyPatTwiceNoRefs = destructTyPatTwice' Utils.destructTyPatNoRefs
end
