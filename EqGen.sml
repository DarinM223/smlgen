structure EqGenBuild =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  fun andalsoChainExp l =
    case List.filter (fn Const t => not (Token.same (t, trueTok)) | _ => true) l of
      [] => Const trueTok
    | l => infixLExp andalsoTok l

  val eqTypes =
    let
      val arrayLikeTypes =
        ["Word8", "Char", "WideChar", "Bool", "Int", "Word", "Real"]
      fun combineType prefix suffix =
        List.map (fn typ => prefix ^ suffix ^ "." ^ typ)
      fun arrayTypes suffix typesIfEq types =
        List.concat
          (List.map
             (fn "Real" => combineType "Real" suffix types
               | prefix => combineType prefix suffix (typesIfEq @ types))
             arrayLikeTypes)
    in
      [ "string"
      , "int"
      , "char"
      , "word"
      , "bool"
      , "order"
      , "array"
      , "Date.weekday"
      , "Date.month"
      , "IEEEReal.real_order"
      , "IEEEReal.float_class"
      , "IEEEReal.rounding_mode"
      , "IEEEReal.decimal_approx"
      , "Int32.int"
      , "Int63.int"
      , "Int64.int"
      , "LargeInt.int"
      , "FixedInt.int"
      , "Position.int"
      , "IntInf.int"
      , "IO.buffer_mode"
      , "OS.syserror"
      , "OS.FileSys.access_mode"
      , "OS.FileSys.file_id"
      , "OS.IO.iodesc"
      , "OS.IO.iodesc_kind"
      , "OS.IO.poll_desc"
      , "TextPrimIO.pos"
      , "WideTextPrimIO.pos"
      , "WideString.string"
      , "WideChar.char"
      , "StringCvt.radix"
      , "StringCvt.realfmt"
      , "Time.time"
      , "Word8.word"
      , "Word32.word"
      , "Word63.word"
      , "Word64.word"
      , "LargeWord.word"
      ] @ arrayTypes "Array" ["elem"] ["array", "vector"]
      @ arrayTypes "ArraySlice" ["elem"] ["array", "vector"]
      @ arrayTypes "Vector" ["elem", "vector"] []
      @ arrayTypes "VectorSlice" ["elem", "vector"] []
    end
  val compareTypes =
    [ ("Date.date", "Date.compare")
    , ("Substring.substring", "Substring.compare")
    , ("WideSubstring.substring", "WideSubstring.compare")
    , ("CharVectorSlice.slice", "Substring.compare")
    , ("WideCharVectorSlice.slice", "WideSubstring.compare")
    ]
  val rewrites = [("real", "Real.=="), ("LargeReal.real", "LargeReal.==")]

  val eqTypesSet = (AtomRedBlackSet.fromList o List.map Atom.atom) eqTypes
  val compareTypesMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty compareTypes
  val rewriteMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty rewrites

  fun mkEq t =
    let
      val (prefix, t) = splitPrefixFromType t
      val prepended =
        if t = "t" then (if String.size prefix = 0 then "op==" else "==")
        else "eq" ^ capitalize t
    in
      mkToken (prefix ^ prepended)
    end
  val prefixGen = mkEq
  val defaultGenFnName = "op="

  val eqOptionDec =
    let
      val conTok = mkToken "eqOption"
      val eqTok = mkToken "eq"
      val (xTok, yTok) = (mkToken "x", mkToken "y")
    in
      multFunDec
        [[ ( conTok
           , [ Pat.Const eqTok
             , destructTuplePat
                 [ destructConPat someTok (Pat.Const xTok)
                 , destructConPat someTok (Pat.Const yTok)
                 ]
             ]
           , appExp [Const eqTok, tupleExp [Const xTok, Const yTok]]
           )
         , ( conTok
           , [wildPat, destructTuplePat [Pat.Const noneTok, Pat.Const noneTok]]
           , Const trueTok
           )
         , (conTok, [wildPat, wildPat], Const falseTok)
         ]]
    end
  val eqListDec =
    let
      val conTok = mkToken "eqList"
      val eqTok = mkToken "eq"
      val (xTok, xsTok) = (mkToken "x", mkToken "xs")
      val (yTok, ysTok) = (mkToken "y", mkToken "ys")
    in
      multFunDec
        [[ ( conTok
           , [ Pat.Const eqTok
             , destructTuplePat
                 [ destructInfixLPat consTok [Pat.Const xTok, Pat.Const xsTok]
                 , destructInfixLPat consTok [Pat.Const yTok, Pat.Const ysTok]
                 ]
             ]
           , infixLExp andalsoTok
               [ appExp [Const eqTok, tupleExp [Const xTok, Const yTok]]
               , appExp
                   [ Const conTok
                   , Const eqTok
                   , tupleExp [Const xsTok, Const ysTok]
                   ]
               ]
           )
         , ( conTok
           , [wildPat, destructTuplePat [Pat.Const nilTok, Pat.Const nilTok]]
           , Const trueTok
           )
         , (conTok, [wildPat, wildPat], Const falseTok)
         ]]
    end

  fun additionalDecs env =
    let
      fun addEqOption a =
        if Env.getOption env "option" then eqOptionDec :: a else a
      fun addEqList a =
        if Env.getOption env "list" then eqListDec :: a else a
    in
      (addEqList o addEqOption) []
    end

  fun tyCon env e1 e2 "list" [a] =
        ( Env.setOption env ("list", true)
        ; appExp
            [ Const (mkToken "eqList")
            , parensExp (tyExp env a)
            , tupleExp [e1, e2]
            ]
        )
    | tyCon env e1 e2 "option" [a] =
        ( Env.setOption env ("option", true)
        ; appExp
            [ Const (mkToken "eqOption")
            , parensExp (tyExp env a)
            , tupleExp [e1, e2]
            ]
        )
    | tyCon _ e1 e2 "ref" [_] = infixLExp equalTok [e1, e2]
    | tyCon (env as Env {env = env', ...}) e1 e2 (s: string) (args: Ty.ty list) =
        let
          val atom = Atom.atom s
          val con = Const
            (if tyconIsGeneratedFix env' s then
               mkToken s
             else if AtomRedBlackMap.inDomain (rewriteMap, atom) then
               mkToken (AtomRedBlackMap.lookup (rewriteMap, atom))
             else
               mkEq (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp env) args)]
        in
          if AtomRedBlackSet.member (eqTypesSet, atom) then
            infixLExp equalTok [e1, e2]
          else if AtomRedBlackMap.inDomain (compareTypesMap, atom) then
            infixLExp equalTok
              [ appExp
                  [ Const (mkToken
                      (AtomRedBlackMap.lookup (compareTypesMap, atom)))
                  , tupleExp [e1, e2]
                  ]
              , Const CompareGenBuild.equalCmpTok
              ]
          else
            appExp [constrExp, tupleExp [e1, e2]]
        end
  and tyExp env ty =
    let
      val env = Env.freshEnv env
      fun etaReduce a b elems exp newExp =
        case Seq.toList elems of
          [Const a', Const b'] =>
            if Token.same (a, a') andalso Token.same (b, b') then newExp
            else singleFnExp (destructTuplePat [Pat.Const a, Pat.Const b]) exp
        | _ => singleFnExp (destructTuplePat [Pat.Const a, Pat.Const b]) exp
    in
      case (Env.destructTyPatTwiceNoRefs env ty, tyExp_ env ty) of
        ( (Pat.Const a, Pat.Const b)
        , exp as App {left, right = Tuple {elems, ...}, ...}
        ) => etaReduce a b elems exp left
      | ((Pat.Const a, Pat.Const b), exp as Infix {left, id, right}) =>
          if Token.same (id, equalTok) then
            etaReduce a b (Seq.fromList [left, right]) exp (Const opEqualTok)
          else
            singleFnExp (destructTuplePat [Pat.Const a, Pat.Const b]) exp
      | ((pat1, pat2), exp) => singleFnExp (destructTuplePat [pat1, pat2]) exp
    end
  and tyExp_ (Env {vars = vars as ref (a :: b :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), tupleExp [Const a, Const b]])
    | tyExp_ _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp_ env (Ty.Record {elems, ...}) =
        andalsoChainExp (List.map (tyExp_ env o #ty) (Seq.toList elems))
    | tyExp_ env (Ty.Tuple {elems, ...}) =
        andalsoChainExp (List.map (tyExp_ env) (Seq.toList elems))
    | tyExp_ (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val id = Option.getOpt (rewriteAlias (Atom.atom id), id)
          val args = syntaxSeqToList args
          fun con e1 e2 =
            case generatedFixNameForTy env' ty of
              SOME ty => appExp [Const ty, tupleExp [e1, e2]]
            | NONE => tyCon env e1 e2 id args
        in
          case (id, args) of
            ("unit", []) => Const trueTok
          | _ =>
              (case !vars of
                 a :: b :: t => (vars := t; con (Const a) (Const b))
               | _ => raise Fail "No vars in con")
        end
    | tyExp_ _ (Ty.Arrow _) = Const trueTok
    | tyExp_ env (Ty.Parens {ty, ...}) = tyExp_ env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val env = Env.freshEnv env
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             let
               val (pat1, pat2) = destructTyPatTwiceNoRefs env ty
             in
               ( destructTuplePat [conPat id pat1, conPat id pat2]
               , tyExp_ env ty
               )
             end
            | {arg = NONE, id, ...} =>
             (destructTuplePat [Pat.Const id, Pat.Const id], Const trueTok))
          constrs
      val tups =
        if List.length constrs > 1 then tups @ [(wildPat, Const falseTok)]
        else tups
    in
      multFnExp tups
    end
end

structure EqGen = BasicGeneratorFn(EqGenBuild)
