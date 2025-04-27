structure EqGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val andalsoChainExp = infixLExp andalsoTok
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
      , "Array.array"
      , "Array.vector"
      , "Vector.vector"
      , "Bool.bool"
      , "Char.char"
      , "Char.string"
      , "Date.weekday"
      , "Date.month"
      , "General.unit"
      , "General.order"
      , "IEEEReal.real_order"
      , "IEEEReal.float_class"
      , "IEEEReal.rounding_mode"
      , "IEEEReal.decimal_approx"
      , "Int.int"
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
      , "BinPrimIO.array"
      , "BinPrimIO.vector"
      , "BinPrimIO.elem"
      , "BinPrimIO.pos"
      , "TextPrimIO.array"
      , "TextPrimIO.vector"
      , "TextPrimIO.elem"
      , "TextPrimIO.pos"
      , "WideTextPrimIO.array"
      , "WideTextPrimIO.vector"
      , "WideTextPrimIO.elem"
      , "WideTextPrimIO.pos"
      , "String.string"
      , "String.char"
      , "WideString.string"
      , "WideString.char"
      , "StringCvt.radix"
      , "StringCvt.realfmt"
      , "Substring.string"
      , "Substring.char"
      , "WideSubstring.string"
      , "WideSubstring.char"
      , "Text.Char.char"
      , "Text.String.string"
      , "Text.CharVector.vector"
      , "Text.CharArray.array"
      , "WideText.Char.char"
      , "WideText.String.string"
      , "WideText.CharVector.vector"
      , "WideText.CharArray.array"
      , "Time.time"
      , "Word.word"
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
  val rewrites =
    [ ("real", "Real.==")
    , ("Real.real", "Real.==")
    , ("Math.real", "Real.==")
    , ("LargeReal.real", "LargeReal.==")
    ]

  val eqTypesSet = (AtomRedBlackSet.fromList o List.map Atom.atom) eqTypes
  val compareTypesMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty compareTypes
  val rewriteMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty rewrites

  val mkEq = prependTokenOrDefault "==" "eq"

  fun additionalDecs env = []

  fun tyCon env e1 e2 "list" [a] =
        ( Env.setOption env ("list", true)
        ; appExp
            [ Const (mkToken "eqList")
            , parensExp (tyExp' env a)
            , tupleExp [e1, e2]
            ]
        )
    | tyCon env e1 e2 "List.list" [a] =
        tyCon env e1 e2 "list" [a]
    | tyCon env e1 e2 "option" [a] =
        ( Env.setOption env ("option", true)
        ; appExp
            [ Const (mkToken "eqOption")
            , parensExp (tyExp' env a)
            , tupleExp [e1, e2]
            ]
        )
    | tyCon env e1 e2 "Option.option" [a] =
        tyCon env e1 e2 "option" [a]
    | tyCon env e1 e2 "ref" [_] = infixLExp equalTok [e1, e2]
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
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
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
              , Const CompareGen.equalCmpTok
              ]
          else
            appExp [constrExp, tupleExp [e1, e2]]
        end
  and tyExp' env ty =
    let
      val env = Env.freshEnv env
    in
      case (Env.destructTyPatTwiceNoRefs env ty, tyExp env ty) of
        ( (pat1 as Pat.Const a, pat2 as Pat.Const b)
        , exp as App {left, right = Tuple {elems, ...}, ...}
        ) =>
          (case Seq.toList elems of
             [Const a', Const b'] =>
               if Token.same (a, a') andalso Token.same (b, b') then left
               else singleFnExp (destructTuplePat [pat1, pat2]) exp
           | _ => singleFnExp (destructTuplePat [pat1, pat2]) exp)
      | ((pat1, pat2), exp) => singleFnExp (destructTuplePat [pat1, pat2]) exp
    end
  and tyExp (Env {vars = vars as ref (a :: b :: t), ...}) (Ty.Var v) =
        (vars := t; appExp [Const (mkTyVar v), tupleExp [Const a, Const b]])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        andalsoChainExp (List.map (tyExp env o #ty) (Seq.toList elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        andalsoChainExp (List.map (tyExp env) (Seq.toList elems))
    | tyExp (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
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
    | tyExp _ (Ty.Arrow _) = raise Fail "Functions cannot be equal"
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val env = Env.freshEnv env
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             let
               val (pat1, pat2) = destructTyPatTwiceNoRefs env ty
             in
               (destructTuplePat [conPat id pat1, conPat id pat2], tyExp env ty)
             end
            | {arg = NONE, id, ...} =>
             (destructTuplePat [Pat.Const id, Pat.Const id], Const trueTok))
          constrs
      val tups = tups @ [(wildPat, Const falseTok)]
    in
      multFnExp tups
    end

  fun genTypebind ({elems, ...}: typbind) =
    let
      val env = Env.empty (mkEnv (! Options.defaultTableSize))
      val decs =
        List.map
          (fn {ty, tycon, tyvars, ...} =>
             let
               val vars = syntaxSeqToList tyvars
               val env = Env.setSubEnv (Env.freshEnv env) (envWithVars vars)
             in
               valDec (Pat.Const (mkEq tycon)) (header vars (tyExp' env ty))
             end) (Seq.toList elems)
    in
      localDecs (additionalDecs env) (multDec decs)
    end

  fun genSimpleDatabind (env, tyTok, vars, Databind constrs) =
        let
          val env = Env.empty env
          val dec = valDec (Pat.Const (mkEq tyTok)) (header vars
            (genConstrs (env, constrs)))
        in
          localDecs (additionalDecs env) dec
        end
    | genSimpleDatabind (_, tyTok, vars, Typebind ty) =
        genSingleTypebind genTypebind (tyTok, vars, ty)

  fun genRecursiveDatabind (env, tycons, tys, vars) =
    let
      val env as Env {env = env', ...} = Env.empty env
      val varExps = List.map Ty.Var vars
      val dups: IntRedBlackSet.set AtomTable.hash_table =
        AtomTable.mkTable (List.length tycons, LibBase.NotFound)
      val generatorDecs =
        List.map
          (fn (tycon, ty) =>
             let
               val tyconA = Atom.atom (Token.toString tycon)
               val args =
                 List.map
                   (fn Ty.Con {id, ...} => MaybeLongToken.getToken id
                     | Ty.Var v => mkTyVar v
                     | _ => raise Fail "Invalid arg")
                   (generatedArgsForTy env' ty)
               val argDups = findDuplicates args
               val () = AtomTable.insert dups (tyconA, argDups)
               val substMap = buildSubstMap env' (Token.toString tycon) varExps
             in
               ( Pat.Const tycon
               , singleFnExp
                   (destructTuplePat
                      (applyDuplicates (argDups, Pat.Const, args)))
                   (case tyconData env' tyconA of
                      Databind constrs =>
                        genConstrs
                          (env, List.map (substConstr substMap) constrs)
                    | Typebind ty => tyExp' env (subst substMap ty))
               )
             end) (ListPair.zip (tycons, tys))
      val concatTys = mkToken (String.concatWith "_"
        (List.map Token.toString tycons))
      val mutRecDec = valDecs true
        (List.map
           (fn (tycon, args) =>
              let
                val tycon' = baseTyName (Token.toString tycon)
                val argDups = AtomTable.lookup dups (Atom.atom tycon')
                val env = Env.freshEnv env
                val args = applyDuplicates (argDups, tyExp' env, args)
              in
                ( Pat.Const tycon
                , singleFnExp (Pat.Const quesTok) (appExp
                    [Const (mkToken tycon'), tupleExp args, Const quesTok])
                )
              end) (generatedFixesAndArgs env'))
      val tyToks = List.map (Option.valOf o generatedFixNameForTy env') tys
      val dec = multDec
        (additionalDecs env
         @
         [ valDecs true generatorDecs
         , valDec (Pat.Const concatTys)
             (singleFnExp
                (destructTuplePat (List.map (Pat.Const o mkTyVar) vars))
                (singleLetExp mutRecDec (tupleExp (List.map Const tyToks))))
         ])
      val unpacked = unpackingDecs (env', vars, concatTys, tycons, mkEq, "op=")
    in
      localDec dec (multDec unpacked)
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
