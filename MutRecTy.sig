signature MUT_REC_TY =
sig
  type env

  datatype type_data = Databind of BuildAst.constr list | Typebind of Ast.Ty.ty
  exception RecursionLimit

  val mkEnv: int -> env
  val envWithVars: Token.token list -> env -> env

  val buildSubstMap: env -> string -> Ast.Ty.ty list -> Ast.Ty.ty AtomMap.map
  val subst: Ast.Ty.ty AtomMap.map -> Ast.Ty.ty -> Ast.Ty.ty
  val substConstr: Ast.Ty.ty AtomMap.map -> BuildAst.constr -> BuildAst.constr

  val findDuplicates: Token.token list -> IntRedBlackSet.set
  val applyDuplicates: IntRedBlackSet.set * ('a -> 'b) * 'a list -> 'b list

  val generatedFixNameForTy: env -> Ast.Ty.ty -> Token.token option
  val generatedArgsForTy: env -> Ast.Ty.ty -> Ast.Ty.ty list
  val generatedFixesAndArgs: env -> (Token.token * Ast.Ty.ty list) list
  val tyconIsGeneratedFix: env -> string -> bool
  val tyconData: env -> Atom.atom -> type_data

  val baseTyName: string -> string

  val unpackingDecs:
    (env
     * Token.token list
     * Token.token
     * Token.token list
     * (Token.token -> Token.token)
     * string)
    -> Ast.Exp.dec list

  val maxTySizeErrorMsg: string
  val genDatabindHelper:
    (env * Token.token * Token.token list * type_data -> Ast.Exp.dec)
    * (env * Token.token list * Ast.Ty.ty list * Token.token list -> Ast.Exp.dec)
    -> Ast.Exp.datbind
    -> Ast.Exp.typbind option
    -> Ast.Exp.dec
  val genSingleTypebind: (Ast.Exp.typbind -> Ast.Exp.dec)
                         -> Token.token * Token.token list * Ast.Ty.ty
                         -> Ast.Exp.dec
end
