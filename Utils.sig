signature UTILS =
sig
  val capitalize: string -> string
  val mkTyVar: Token.t -> Token.t
  val prependToken: string -> Token.token -> Token.token
  val sameTokens: Token.token list * Token.token list -> bool
  val syntaxSeqToList: 'a Ast.SyntaxSeq.t -> 'a list
  val syntaxSeqLen: 'a Ast.SyntaxSeq.t -> int
  val listToSyntaxSeq: 'a list -> 'a Ast.SyntaxSeq.t
  val syntaxSeqMap: ('a -> 'b) -> 'a Ast.SyntaxSeq.t -> 'b Ast.SyntaxSeq.t
  val syntaxSeqMapTy: ('a -> Ast.Ty.ty)
                      -> 'a Ast.SyntaxSeq.t
                      -> Ast.Ty.ty Ast.SyntaxSeq.t
  val showTy: Ast.Ty.ty -> string
  val tySize: Ast.Ty.ty -> int
  val stripParens: Ast.Pat.pat -> Ast.Pat.pat
  val destructTyPat: (Token.token -> Token.token) -> Ast.Ty.ty -> Ast.Pat.pat
  val combineDecs: Ast.Exp.dec -> Ast.Exp.dec -> Ast.Exp.dec
  val pretty: Ast.ast -> TerminalColorString.t
  val prettyDec: Ast.Exp.dec -> TerminalColorString.t
  val prettyDatbind: Ast.Exp.datbind -> TerminalColorString.t
  val concatDatbinds: Ast.Exp.datbind list -> Ast.Exp.datbind
  val datbindTys: Ast.Exp.datbind -> Ast.Ty.ty list
  val mapBase: (string -> string) -> string -> string
  val mapBasename: (string -> string) -> FilePath.filepath -> FilePath.filepath
  val qualifiedTypePart: string -> string
  val typenameTypePart: string -> string

  type gen =
    { genTypebind: Ast.Exp.typbind -> Ast.Exp.dec
    , genDatabind: Ast.Exp.datbind -> Ast.Exp.typbind option -> Ast.Exp.dec
    }
  val emptyGen: gen
  val addGen: gen -> gen -> gen
end
