structure HashGen =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils MutRecTy Env

  val mkHash = prependToken "hash"
  val hashTok = mkToken "hash"
  val resultTok = mkToken "result"
  val combineTok = mkToken "combine"
  val zeroWordTok = mkToken "0w0"
  val oneWordTok = mkToken "0w1"
  val oneIntTok = mkToken "1"
  val wordModTok = mkToken "Word.mod"
  val wordSizeTok = mkToken "Word.wordSize"
  val primeTok = mkToken "0w31"
  val mTok = mkToken "0w1000000009"
  val hashStringTok = mkToken "hashString"
  val wordFromIntTok = mkToken "Word.fromInt"
  val ordTok = mkToken "Char.ord"
  val trueHashTok = mkToken "0wx096DB16D"
  val falseHashTok = mkToken "0wx01B56B6D"
  val unitHashTok = mkToken "0wx65B2531B"
  val nilHashTok = mkToken "0wx6D52A54D"
  val noneHashTok = mkToken "0wx1A35B599"
  val functionHashTok = mkToken "0wx4996071B"

  fun hashString env e =
    (Env.setOption env ("string", true); appExp [Const hashStringTok, e])

  val combineDec =
    let
      val (aTok, bTok) = (mkToken "a", mkToken "b")
    in
      valDec (Pat.Const combineTok)
        (singleFnExp (destructTuplePat [Pat.Const aTok, Pat.Const bTok])
           (infixLExp addTok
              [infixLExp mulTok [Const primeTok, Const aTok], Const bTok]))
    end
  fun combine env a b =
    ( Env.setOption env ("combine", true)
    ; appExp [Const combineTok, tupleExp [a, b]]
    )

  val hashStringDec =
    let
      val (chTok, hTok, pTok) = (mkToken "ch", mkToken "h", mkToken "p")
      val modByM = fn e => appExp [Const wordModTok, tupleExp [e, Const mTok]]
      val number1Tok = mkToken "#1"
    in
      valDec (Pat.Const hashStringTok) (infixLExp oTok
        [ Const number1Tok
        , appExp
            [ Const (mkToken "Substring.foldl")
            , parensExp
                (singleFnExp
                   (destructTuplePat
                      [ Pat.Const chTok
                      , destructTuplePat [Pat.Const hTok, Pat.Const pTok]
                      ])
                   (tupleExp
                      [ modByM (infixLExp addTok
                          [ Const hTok
                          , infixLExp mulTok
                              [ appExp
                                  [ Const wordFromIntTok
                                  , parensExp (infixLExp addTok
                                      [ appExp [Const ordTok, Const chTok]
                                      , Const oneIntTok
                                      ])
                                  ]
                              , Const pTok
                              ]
                          ])
                      , modByM (infixLExp mulTok [Const pTok, Const primeTok])
                      ]))
            , tupleExp [Const zeroWordTok, Const oneWordTok]
            ]
        , Const (mkToken "Substring.full")
        ])
    end
  val hashListDec =
    let
      val conTok = mkToken "hashList"
      val (lTok, iTok, accTok) = (mkToken "l", mkToken "i", mkToken "acc")
    in
      fn env =>
        multFunDec
          [[ (conTok, [wildPat, Pat.Const nilTok], Const nilHashTok)
           , ( conTok
             , [Pat.Const hashTok, Pat.Const lTok]
             , appExp
                 [ Const (mkToken "List.foldl")
                 , parensExp
                     (singleFnExp
                        (destructTuplePat [Pat.Const iTok, Pat.Const accTok])
                        (combine env (Const accTok)
                           (appExp [Const hashTok, Const iTok])))
                 , parensExp (appExp
                     [ Const wordFromIntTok
                     , parensExp (appExp
                         [Const (mkToken "List.length"), Const lTok])
                     ])
                 , Const lTok
                 ]
             )
           ]]
    end
  val hashOptionDec =
    let
      val conTok = mkToken "hashOption"
      val optTok = mkToken "opt"
    in
      multFunDec
        [[( conTok
          , [Pat.Const hashTok, Pat.Const optTok]
          , appExp
              [ Const (mkToken "Option.getOpt")
              , tupleExp
                  [ appExp
                      [ Const (mkToken "Option.map")
                      , Const hashTok
                      , Const optTok
                      ]
                  , Const noneHashTok
                  ]
              ]
          )]]
    end
  fun getPrefixModule s =
    let
      val (prefix, _) = splitPrefixFromTypeString s
    in
      if String.size prefix > 0 then
        String.extract (prefix, 0, SOME (String.size prefix - 1))
      else
        prefix
    end

  fun hashCustomIntDec env intType =
    let
      val (prefix, _) = splitPrefixFromTypeString intType
      val withPrefix = fn s => mkToken (prefix ^ s)
      val dec = mkHash (mkToken (getPrefixModule intType))
      val (iTok, pTok) = (mkToken "i", mkToken "p")
      val () = Env.setOption env ("string", true)
    in
      valDec (Pat.Const dec) (caseExp (Const (withPrefix "precision"))
        [ ( conPat someTok (Pat.Const pTok)
          , ifThenElseExp
              (infixLExp opGtTok
                 [ Const pTok
                 , infixLExp addTok [Const wordSizeTok, Const oneIntTok]
                 ])
              (infixLExp oTok
                 [ parensExp (singleFnExp (Pat.Const iTok) (appExp
                     [ Const (mkToken "Word.fromLargeInt")
                     , parensExp (appExp
                         [ Const (mkToken "IntInf.xorb")
                         , tupleExp
                             [ Const iTok
                             , appExp
                                 [ Const (mkToken "IntInf.~>>")
                                 , tupleExp
                                     [ Const iTok
                                     , appExp
                                         [ Const wordFromIntTok
                                         , Const wordSizeTok
                                         ]
                                     ]
                                 ]
                             ]
                         ])
                     ]))
                 , Const (withPrefix "toLarge")
                 ])
              (infixLExp oTok [Const wordFromIntTok, Const (withPrefix "toInt")])
          )
        , ( Pat.Const noneTok
          , infixLExp oTok [Const hashStringTok, Const (withPrefix "toString")]
          )
        ])
    end

  fun hashCustomWordDec wordType =
    let
      val (prefix, _) = splitPrefixFromTypeString wordType
      val withPrefix = fn s => mkToken (prefix ^ s)
      val dec = mkHash (mkToken (getPrefixModule wordType))
      val wTok = mkToken "w"
      val toWord = [Const wordFromIntTok, Const (withPrefix "toInt")]
    in
      valDec (Pat.Const dec)
        (ifThenElseExp
           (infixLExp opGtTok
              [ Const (withPrefix "wordSize")
              , infixLExp addTok [Const wordSizeTok, Const oneIntTok]
              ])
           (infixLExp oTok
              (toWord
               @
               [parensExp (singleFnExp (Pat.Const wTok) (appExp
                  [ Const (withPrefix "xorb")
                  , tupleExp
                      [ Const wTok
                      , appExp
                          [ Const (withPrefix ">>")
                          , tupleExp
                              [ Const wTok
                              , appExp [Const wordFromIntTok, Const wordSizeTok]
                              ]
                          ]
                      ]
                  ]))])) (infixLExp oTok toWord))
    end

  fun combineExpsInLet _ [] =
        raise Fail "combineExpsInLet: expected non empty list of expressions"
    | combineExpsInLet env (head :: rest) =
        let
          val headDec = valDec (identPat resultTok) head
          val restDecs =
            List.map
              (fn exp =>
                 valDec (identPat resultTok) (combine env (Const resultTok) exp))
              rest
        in
          singleLetExp (multDec (headDec :: restDecs)) (Const resultTok)
        end

  val customIntegerTypes = (AtomRedBlackSet.fromList o List.map Atom.atom)
    [ "Int32.int"
    , "Int63.int"
    , "Int64.int"
    , "LargeInt.int"
    , "FixedInt.int"
    , "Position.int"
    , "IntInf.int"
    ]
  val customWordTypes = (AtomRedBlackSet.fromList o List.map Atom.atom)
    [ "Word8.word"
    , "Word32.word"
    , "Word63.word"
    , "Word64.word"
    , "LargeWord.word"
    ]

  fun additionalDecs env =
    let
      fun addCombineHash a =
        if Env.getOption env "combine" then combineDec :: a else a
      fun addHashString a =
        if Env.getOption env "string" then hashStringDec :: a else a
      fun addHashOption a =
        if Env.getOption env "option" then hashOptionDec :: a else a
      val addHashList =
        if Env.getOption env "list" then
          (* Turn on combine option before adding hashList function *)
          let val hashListDec = hashListDec env
          in fn a => hashListDec :: a
          end
        else
          fn a => a
      val customIntDecs = List.map (hashCustomIntDec env)
        (List.filter
           (fn typ => AtomRedBlackSet.member (customIntegerTypes, Atom.atom typ))
           (Env.getOptions env))
      val customWordDecs = List.map hashCustomWordDec
        (List.filter
           (fn typ => AtomRedBlackSet.member (customWordTypes, Atom.atom typ))
           (Env.getOptions env))
    in
      (List.rev o (fn a => customWordDecs @ a) o (fn a => customIntDecs @ a)
       o addHashList o addHashOption o addHashString o addCombineHash) []
    end

  fun tyCon _ v "int" [] =
        [appExp [Const wordFromIntTok, Const v]]
    | tyCon _ v "bool" [] =
        [ifThenElseExp (Const v) (Const trueHashTok) (Const falseHashTok)]
    | tyCon _ v "char" [] =
        [appExp
           [Const wordFromIntTok, parensExp (appExp [Const ordTok, Const v])]]
    | tyCon _ v "word" [] = [Const v]
    | tyCon env v "string" [] =
        [hashString env (Const v)]
    | tyCon env v "list" [a] =
        ( Env.setOption env ("list", true)
        ; [appExp
             [Const (mkToken "hashList"), parensExp (tyExp' env a), Const v]]
        )
    | tyCon env v "option" [a] =
        ( Env.setOption env ("option", true)
        ; [appExp
             [Const (mkToken "hashOption"), parensExp (tyExp' env a), Const v]]
        )
    | tyCon (env as Env {env = env', ...}) v (s: string) (args: Ty.ty list) =
        let
          val atom = Atom.atom s
          val con = Const
            (if tyconIsGeneratedFix env' s then mkToken s
             else mkHash (mkToken s))
          val constrExp =
            case args of
              [] => con
            | _ => appExp [con, tupleExp (List.map (tyExp' env) args)]
        in
          if
            AtomRedBlackSet.member (customIntegerTypes, atom)
            orelse AtomRedBlackSet.member (customWordTypes, atom)
          then
            ( Env.setOption env (s, true)
            ; [appExp [Const (mkHash (mkToken (getPrefixModule s))), Const v]]
            )
          else if
            AtomRedBlackMap.inDomain (ShowGen.rewriteMap, atom)
          then
            [hashString env (parensExp (appExp
               [ Const (mkToken
                   (AtomRedBlackMap.lookup (ShowGen.rewriteMap, atom)))
               , Const v
               ]))]
          else
            [appExp [constrExp, Const v]]
        end
  and tyExp' env ty =
    let
      val env = Env.freshEnv env
    in
      case (destructTyPat (Env.fresh env) ty, tyExp (envVars env) ty) of
        (Pat.Const _, [App {left, right = Const _, ...}]) => left
      | (pat, [exp]) => singleFnExp pat exp
      | (pat, [exp1, exp2]) => singleFnExp pat (combine env exp1 exp2)
      | (pat, exps) => singleFnExp pat (combineExpsInLet env exps)
    end
  and tyExp (Env {vars = vars as ref (h :: t), ...}) (Ty.Var v) =
        (vars := t; [appExp [Const (mkTyVar v), Const h]])
    | tyExp _ (Ty.Var _) = raise Fail "No vars for var"
    | tyExp env (Ty.Record {elems, ...}) =
        List.concat (List.map (tyExp env o #ty) (Seq.toList elems))
    | tyExp env (Ty.Tuple {elems, ...}) =
        List.concat (List.map (tyExp env) (Seq.toList elems))
    | tyExp (env as Env {vars, env = env', ...}) (ty as Ty.Con {id, args, ...}) =
        let
          val id = Token.toString (MaybeLongToken.getToken id)
          val id = Option.getOpt (rewriteAlias (Atom.atom id), id)
          val args = syntaxSeqToList args
          fun con v =
            case generatedFixNameForTy env' ty of
              SOME ty => [appExp [Const ty, Const v]]
            | NONE => tyCon env v id args
        in
          case (id, args) of
            ("ref", [ty]) => tyExp env ty
          | ("unit", []) => [Const unitHashTok]
          | _ =>
              (case !vars of
                 h :: t => (vars := t; con h)
               | [] => raise Fail "No vars in con")
        end
    | tyExp _ (Ty.Arrow _) = [Const functionHashTok]
    | tyExp env (Ty.Parens {ty, ...}) = tyExp env ty

  fun genConstrs (env, constrs: constr list) : Exp.exp =
    let
      val env = Env.freshEnv env
      fun hashConstr constr f def =
        if List.length constrs > 1 then
          f (hashString env (Const (mkToken
            ("\"" ^ Token.toString constr ^ "\""))))
        else
          def
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             ( conPat id (destructTyPat (Env.fresh env) ty)
             , case tyExp (envVars env) ty of
                 [exp] =>
                   hashConstr id (fn constr => combine env constr exp) exp
               | [exp1, exp2] =>
                   hashConstr id
                     (fn constr => combineExpsInLet env [constr, exp1, exp2])
                     (combine env exp1 exp2)
               | exps =>
                   combineExpsInLet env
                     (hashConstr id (fn constr => constr :: exps) exps)
             )
            | {arg = NONE, id, ...} =>
             (Pat.Const id, hashConstr id (fn e => e) (Const zeroWordTok)))
          constrs
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
               valDec (Pat.Const (mkHash tycon)) (header vars (tyExp' env ty))
             end) (Seq.toList elems)
    in
      localDecs (additionalDecs env) (multDec decs)
    end

  fun genSimpleDatabind (env, tyTok, vars, Databind constrs) =
        let
          val env = Env.empty env
          val dec = valDec (Pat.Const (mkHash tyTok)) (header vars
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
      val unpacked = unpackingDecs
        (env', vars, concatTys, tycons, mkHash, "Word.fromInt")
    in
      localDec dec (multDec unpacked)
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
