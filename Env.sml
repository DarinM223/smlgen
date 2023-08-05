structure Env =
struct
  datatype t =
    Env of
      { c: int ref
      , vars: Token.t list ref
      , options: bool AtomTable.hash_table
      , env: MutRecTy.env
      }
  fun empty env =
    Env
      { c = ref 0
      , vars = ref []
      , options = AtomTable.mkTable (20, LibBase.NotFound)
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
      val tok = Utils.appendTokens t (BuildAst.mkToken (Int.toString i))
    in
      (vars := tok :: !vars; tok)
    end
  fun setOption (Env {options, ...}) (opt, flag) =
    AtomTable.insert options (Atom.atom opt, flag)
  fun getOption (Env {options, ...}) opt =
    AtomTable.lookup options (Atom.atom opt)
    handle LibBase.NotFound => false
end
