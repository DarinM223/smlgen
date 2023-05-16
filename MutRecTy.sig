signature MUT_REC_TY =
sig
  type env

  val mkEnv: unit -> env
  val envWithVars: Token.token list -> env -> env

  val buildSubstMap: env -> string -> Ast.Ty.ty list -> Ast.Ty.ty AtomMap.map
  val subst: Ast.Ty.ty AtomMap.map -> Ast.Ty.ty -> Ast.Ty.ty
  val substConstr: Ast.Ty.ty AtomMap.map -> Utils.constr -> Utils.constr

  val findDuplicates: Token.token list -> IntRedBlackSet.set
  val applyDuplicates: IntRedBlackSet.set * ('a -> 'b) * 'a list -> 'b list

  val generatedFixNameForTy: env -> Ast.Ty.ty -> Token.token option
  val generatedArgsForTy: env -> Ast.Ty.ty -> Ast.Ty.ty list
  val generatedFixesAndArgs: env -> (Token.token * Ast.Ty.ty list) list
  val tyconConstrs: env -> Atom.atom -> Utils.constr list

  val baseTyName : string -> string

  val genDatabindHelper:
    (env * Token.token * Token.token list * Utils.constr list -> Ast.Exp.dec)
    * (env * Token.token list * Ast.Ty.ty list * Token.token list -> Ast.Exp.dec)
    -> Ast.Exp.datbind
    -> Ast.Exp.dec
end
