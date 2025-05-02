signature TOKEN_UTILS =
sig
  val stripToken: Token.t -> Token.t
  val mkSource: string -> Source.t
  val mkToken: string -> Token.t
  val mkReservedToken: Token.reserved -> Token.t
  val appendTokens: Token.t -> Token.t -> Token.t
  val stringTok: Token.t -> Token.t
  val stringTokSpace: Token.t -> Token.t
end

signature TOKENS =
sig
  val equalTok: Token.t
  val opEqualTok: Token.t
  val commaTok: Token.t
  val andReservedTok: Token.t
  val recTok: Token.t
  val orTok: Token.t
  val andKeyTok: Token.t
  val andTok: Token.t
  val quesTok: Token.t
  val prodTok: Token.t
  val fatArrowTok: Token.t
  val genericTok: MaybeLongToken.t
  val tieTok: MaybeLongToken.t
  val openTok: Token.t
  val underTok: Token.t
  val tTok: Token.t
  val falseTok: Token.t
  val trueTok: Token.t
  val openParenTok: Token.t
  val closeParenTok: Token.t
  val structureTok: Token.t
  val structTok: Token.t
  val letTok: Token.t
  val inTok: Token.t
  val endTok: Token.t
  val datatypeTok: Token.t
  val openCurlyTok: Token.t
  val closeCurlyTok: Token.t
  val openSquareTok: Token.t
  val closeSquareTok: Token.t
  val fnTok: Token.t
  val valTok: Token.t
  val funTok: Token.t
  val localTok: Token.t
  val caseTok: Token.t
  val ofTok: Token.t
  val andalsoTok: Token.t
  val someTok: Token.t
  val noneTok: Token.t
  val mulTok: Token.t
  val addTok: Token.t
  val oTok: Token.t
  val ifTok: Token.t
  val thenTok: Token.t
  val elseTok: Token.t
end

signature BUILD_AST =
sig
  type constr =
    { arg: {off: Token.token, ty: Ast.Ty.ty} option
    , id: Token.token
    , opp: Token.token option
    }

  val unitExp: Ast.Exp.exp
  val singleLetExp: Ast.Exp.dec -> Ast.Exp.exp -> Ast.Exp.exp
  val ifThenElseExp: Ast.Exp.exp -> Ast.Exp.exp -> Ast.Exp.exp -> Ast.Exp.exp
  val tupleExp: Ast.Exp.exp list -> Ast.Exp.exp
  val recordExp: (Token.token * Ast.Exp.exp) list -> Ast.Exp.exp
  val listExp: Ast.Exp.exp list -> Ast.Exp.exp
  val appExp: Ast.Exp.exp list -> Ast.Exp.exp
  val singleFnExp: Ast.Pat.pat -> Ast.Exp.exp -> Ast.Exp.exp
  val multFnExp: (Ast.Pat.pat * Ast.Exp.exp) list -> Ast.Exp.exp
  val parensExp: Ast.Exp.exp -> Ast.Exp.exp
  val infixLExp: Token.token -> Ast.Exp.exp list -> Ast.Exp.exp
  val unitPat: Ast.Pat.pat
  val parensPat: Ast.Pat.pat -> Ast.Pat.pat
  val identPat: Token.token -> Ast.Pat.pat
  val conPat: Token.token -> Ast.Pat.pat -> Ast.Pat.pat
  val valDec: Ast.Pat.pat -> Ast.Exp.exp -> Ast.Exp.dec
  val valDecs: bool -> (Ast.Pat.pat * Ast.Exp.exp) list -> Ast.Exp.dec
  val multDec: Ast.Exp.dec list -> Ast.Exp.dec
  val singleFunDec: Token.token
                    -> Ast.Pat.pat list
                    -> Ast.Exp.exp
                    -> Ast.Exp.dec
  val multFunDec: (Token.token * Ast.Pat.pat list * Ast.Exp.exp) list list
                  -> Ast.Exp.dec
  val localDec: Ast.Exp.dec -> Ast.Exp.dec -> Ast.Exp.dec
  val localDecs: Ast.Exp.dec list -> Ast.Exp.dec -> Ast.Exp.dec
  val genericDec: Ast.Exp.dec
  val tieDec: Ast.Exp.dec
  val destructRecordPat: Token.token list -> Ast.Pat.pat
  val destructRecordPat': (Token.token * Ast.Pat.pat) list -> Ast.Pat.pat
  val destructTuplePat: Ast.Pat.pat list -> Ast.Pat.pat
  val destructInfixLPat: Token.token -> Ast.Pat.pat list -> Ast.Pat.pat
  val destructListPat: Ast.Pat.pat list -> Ast.Pat.pat
  val destructConPat: Token.token -> Ast.Pat.pat -> Ast.Pat.pat
  val wildPat: Ast.Pat.pat
  val parensTy: Ast.Ty.ty -> Ast.Ty.ty
  val simpleStructStrDec: Token.token -> Ast.Str.strdec -> Ast.Str.strdec
  val simpleDatatypeDec: Ast.Exp.datbind -> Ast.Exp.dec
  val replicateDatatypeDec: Token.token -> Token.token -> Ast.Exp.dec
  val replicateDatatypeToTypbind: Token.t -> MaybeLongToken.t -> Ast.Exp.typbind
end
