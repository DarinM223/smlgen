structure ShowGenBuild =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val mkShow = prependToken "show"
  val prefixGen = mkShow
  val defaultGenFnName = "Int.toString"

  val concatTok = mkToken "^"
  val openSquare = stringTok openSquareTok
  val closeSquare = stringTok closeSquareTok
  val openParen = stringTok openParenTok
  val closeParen = stringTok closeParenTok
  val openCurly = stringTok openCurlyTok
  val closeCurly = stringTok closeCurlyTok
  val quotTok = stringTok (mkToken "\\\"")
  val equalsTok = mkToken " = "
  val commaTok = mkToken ", "
  val concatWithTok = mkToken "String.concatWith"
  val unitTok = stringTok (mkToken "()")

  val showOptionDec =
    let
      val conTok = mkToken "showOption"
      val (fTok, sTok) = (mkToken "f", mkToken "s")
    in
      multFunDec
        [[ ( conTok
           , [ Pat.Const fTok
             , parensPat (destructConPat someTok (Pat.Const sTok))
             ]
           , infixLExp concatTok
               [Const (stringTokSpace someTok), appExp [Const fTok, Const sTok]]
           )
         , (conTok, [wildPat, Pat.Const noneTok], Const (stringTok noneTok))
         ]]
    end

  fun additionalDecs env =
    if Env.getOption env "option" then [showOptionDec] else []

  val rewrites =
    [ ("int", "Int.toString")
    , ("real", "Real.toString")
    , ("word", "Word.toString")
    , ("bool", "Bool.toString")
    , ("Int32.int", "Int32.toString")
    , ("Int63.int", "Int63.toString")
    , ("Int64.int", "Int64.toString")
    , ("LargeInt.int", "LargeInt.toString")
    , ("FixedInt.int", "FixedInt.toString")
    , ("Position.int", "Position.toString")
    , ("IntInf.int", "IntInf.toString")
    , ("Real.real", "Real.toString")
    , ("Math.real", "Real.toString")
    , ("LargeReal.real", "LargeReal.toString")
    , ("Word8.word", "Word8.toString")
    , ("Word32.word", "Word32.toString")
    , ("Word63.word", "Word63.toString")
    , ("Word64.word", "Word64.toString")
    , ("LargeWord.word", "LargeWord.toString")
    , ("Date.date", "Date.toString")
    , ("Substring.substring", "Substring.string")
    , ("WideSubstring.substring", "WideSubstring.string")
    , ("Time.time", "Time.toString")
    , ("IEEEReal.decimal_approx", "IEEEReal.toString")
    ]
  val rewriteMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty rewrites

  fun tyCon _ v "string" [] =
        infixLExp concatTok [Const quotTok, Const v, Const quotTok]
    | tyCon _ v "char" [] =
        infixLExp concatTok
          [ Const (mkToken "\"#\\\"\"")
          , appExp [Const (mkToken "Char.toString"), Const v]
          , Const (mkToken "\"\\\"\"")
          ]
    | tyCon env v "list" [a] =
        infixLExp concatTok
          [ Const openSquare
          , appExp
              [ Const concatWithTok
              , Const (stringTok commaTok)
              , parensExp (appExp
                  [Const (mkToken "List.map"), parensExp (tyExp env a), Const v])
              ]
          , Const closeSquare
          ]
    | tyCon env v "option" [a] =
        ( Env.setOption env ("option", true)
        ; appExp
            [Const (mkToken "showOption"), parensExp (tyExp env a), Const v]
        )
    | tyCon (env as Env {env = env', ...}) v (s: string) (args: Ty.ty list) =
        let
          val atom = Atom.atom s
          val con = Const
            (if tyconIsGeneratedFix env' s then
               mkToken s
             else if AtomRedBlackMap.inDomain (rewriteMap, atom) then
               mkToken (AtomRedBlackMap.lookup (rewriteMap, atom))
             else
               mkShow (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp env) args)]
        in
          appExp [constrExp, Const v]
        end
  and tyExp env ty =
    let
      val env = Env.freshEnv env
    in
      case (destructTyPat (Env.fresh env) ty, tyExp_ (envVars env) ty) of
        (Pat.Const _, App {left, right = Const _, ...}) => left
      | (pat, exp) => singleFnExp pat exp
    end
  and tyExp_ (Env {vars = vars as ref (h :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), Const h])
    | tyExp_ _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp_ env (Ty.Record {elems, ...}) =
        let
          val enclose = fn exp => Const openCurly :: exp :: [Const closeCurly]
          val fields =
            List.map
              (fn {lab, ty, ...} =>
                 infixLExp concatTok
                   [ Const (stringTok (appendTokens lab equalsTok))
                   , tyExp_ env ty
                   ]) (Seq.toList elems)
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp_ env (Ty.Tuple {elems, ...}) =
        let
          val enclose = fn exp => Const openParen :: exp :: [Const closeParen]
          val fields = List.map (tyExp_ env) (Seq.toList elems)
          val exp = appExp
            [Const concatWithTok, Const (stringTok commaTok), listExp fields]
        in
          infixLExp concatTok (enclose exp)
        end
    | tyExp_ (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val id = Option.getOpt (rewriteAlias (Atom.atom id), id)
          val args = syntaxSeqToList args
          fun con v =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, Const v]
            | NONE => tyCon env v id args
        in
          case (id, args) of
            ("ref", [ty]) =>
              infixLExp concatTok [Const (mkToken "\"ref \""), tyExp_ env ty]
          | ("unit", []) => Const unitTok
          | _ =>
              (case !vars of
                 h :: t => (vars := t; con h)
               | [] => raise Fail "No vars in con")
        end
    | tyExp_ _ (ty as Ty.Arrow _) =
        Const (stringTok (mkToken (prettyTy ty)))
    | tyExp_ env (Ty.Parens {ty, ...}) = tyExp_ env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val enclose = fn exp => Const openParen :: exp :: [Const closeParen]
      fun tyToStr (Ty.Con _) = enclose
        | tyToStr _ = fn a => [a]
      val toStr = fn t => mkToken ("\"" ^ Token.toString (stripToken t) ^ " \"")
      val env = Env.freshEnv env
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             ( conPat id (destructTyPat (Env.fresh env) ty)
             , infixLExp concatTok
                 (Const (toStr id) :: tyToStr ty (tyExp_ (envVars env) ty))
             )
            | {id, ...} => (Pat.Const id, Const (stringTok id))) constrs
    in
      multFnExp tups
    end
end

structure ShowGen = BasicGeneratorFn(ShowGenBuild)
