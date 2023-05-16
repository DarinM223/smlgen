signature CONVERT_VALUE =
sig
  type t
  val unit: t
  val const: Token.token -> t
  val app: Token.token -> t -> t
  val parens: t -> t
end
functor ConvertFn(Value: CONVERT_VALUE) =
struct
  open BuildAst

  fun ins ([], {arg = SOME _, ...}) = Value.const quesTok
    | ins ([], _) = Value.unit
    | ins (is, constr: constr) =
        let
          val head =
            case constr of
              {arg = SOME _, ...} => Value.const quesTok
            | _ => Value.unit
          val head = Value.app (List.hd is) head
        in
          List.foldl (fn (i, acc) => Value.app i (Value.parens acc)) head
            (List.tl is)
        end
  fun constr ({arg = SOME _, id, ...}: constr) =
        Value.app id (Value.const quesTok)
    | constr {id, ...} = Value.const id
end

structure GenericGen =
struct
  open BuildAst Utils MutRecTy
  structure ExpValue: CONVERT_VALUE =
  struct
    type t = exp
    val unit = unitExp
    val const = Const
    val app = fn tok => fn a => App {left = Const tok, right = a}
    val parens = parensExp
  end
  structure PatValue: CONVERT_VALUE =
  struct
    open Pat
    type t = pat
    val unit = unitPat
    val const = Const
    val app = fn tok =>
      fn a => Con {opp = NONE, id = MaybeLongToken.make tok, atpat = a}
    val parens = parensPat
  end
  structure ConvertExp = ConvertFn(ExpValue)
  structure ConvertPat = ConvertFn(PatValue)

  fun tyVarFnExp [] exp = exp
    | tyVarFnExp [v] exp =
        singleFnExp (Pat.Const (mkTyVar v)) exp
    | tyVarFnExp vars exp =
        singleFnExp (destructTuplePat (List.map (Pat.Const o mkTyVar) vars)) exp

  fun genTy env parens ty =
    let
      val recordTok = mkToken "record'"
    in
      case ty of
        Ty.Var tok => Const (mkTyVar tok)
      | Ty.Record {elems, ...} =>
          let
            val rTok = mkToken "R'"
            val elems = ArraySlice.foldr (op::) [] elems
            val labels = List.map #lab elems
            val labelExps =
              List.map
                (fn {lab, ty, ...} =>
                   appExp [Const rTok, Const (stringTok lab), genTy env true ty])
                elems
            val exp = parensExp (infixLExp prodTok labelExps)
            val to = singleFnExp (destructRecordPat labels) (infixLExp andTok
              (List.map Const labels))
            val from =
              singleFnExp (destructInfixLPat andTok (List.map Pat.Const labels))
                (recordExp (List.map (fn l => (l, Const l)) labels))
          in
            (if parens then parensExp else fn a => a) (appExp
              [Const recordTok, exp, tupleExp [to, from]])
          end
      | Ty.Tuple {elems, ...} =>
          let
            val elems = ArraySlice.foldr (op::) [] elems
            val len = List.length elems
            val tTok = mkToken "T"
            val freshToks = List.tabulate (len, fn i =>
              mkToken ("t" ^ Int.toString i))
          in
            (if parens then parensExp else fn a => a)
              (if len <= 4 then
                 App
                   { left = Const (mkToken ("tuple" ^ Int.toString len))
                   , right = tupleExp (List.map (genTy env false) elems)
                   }
               else
                 appExp
                   [ Const (mkToken "tuple'")
                   , parensExp (infixLExp prodTok
                       (List.map (fn t => appExp [Const tTok, genTy env true t])
                          elems))
                   , tupleExp
                       [ singleFnExp
                           (destructTuplePat (List.map Pat.Const freshToks))
                           (infixLExp andTok (List.map Const freshToks))
                       , singleFnExp
                           (destructInfixLPat andTok
                              (List.map Pat.Const freshToks))
                           (tupleExp (List.map Const freshToks))
                       ]
                   ])
          end
      | Ty.Con {id, args} =>
          let
            val id = MaybeLongToken.getToken id
          in
            case generatedFixNameForTy env ty of
              SOME ty => Const ty
            | NONE =>
                (case args of
                   SyntaxSeq.Empty => Const id
                 | SyntaxSeq.One ty =>
                     (if parens then parensExp else fn a => a) (App
                       {left = Const id, right = genTy env true ty})
                 | SyntaxSeq.Many {elems, ...} =>
                     (if parens then parensExp else fn a => a) (App
                       { left = Const id
                       , right = tupleExp (List.map (genTy env false)
                           (ArraySlice.foldr (op::) [] elems))
                       }))
          end
      | Ty.Arrow {from, to, ...} =>
          Infix
            { left = genTy env false from
            , id = mkToken "-->"
            , right = genTy env false to
            }
      | Ty.Parens {ty, ...} => genTy env false ty
    end

  fun genConstrs (env, constrs) =
    let
      val c0tok = mkToken "C0'"
      val c1tok = mkToken "C1'"
      val constrs' =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             appExp [Const c1tok, Const (stringTok id), genTy env true ty]
            | {id, ...} =>
             App {left = Const c0tok, right = Const (stringTok id)}) constrs
      val plusTok = mkToken "+`"
      val dataExp =
        List.foldl (fn (e, acc) => Infix {left = acc, id = plusTok, right = e})
          (List.hd constrs') (List.tl constrs')
      val inrTok = mkToken "INR"
      val inlTok = mkToken "INL"
      fun buildINs 0 [_] = [[]]
        | buildINs n [_] =
            [inlTok :: List.tabulate (n - 1, fn _ => inlTok)]
        | buildINs 0 (_ :: cs) =
            [inrTok] :: buildINs 1 cs
        | buildINs n (_ :: cs) =
            (inrTok :: List.tabulate (n, fn _ => inlTok)) :: buildINs (n + 1) cs
        | buildINs _ [] = []
      val revConstrs = List.rev constrs
      val ins = buildINs 0 revConstrs
      val toINs =
        List.map
          (fn (is, constr) =>
             (ConvertPat.constr constr, ConvertExp.ins (is, constr)))
          (ListPair.zip (ins, revConstrs))
      val fromINs =
        List.map
          (fn (is, constr) =>
             (ConvertPat.ins (is, constr), ConvertExp.constr constr))
          (ListPair.zip (ins, revConstrs))
    in
      App
        { left = App {left = Const (mkToken "data'"), right = parensExp dataExp}
        , right = tupleExp [multFnExp toINs, multFnExp fromINs]
        }
    end

  fun genTypebind ({elems, ...}: typbind) =
    let
      val elems = ArraySlice.foldr (op::) [] elems
      val decs =
        List.map
          (fn {tycon, ty, tyvars, ...} =>
             let
               val tyvars = syntaxSeqToList tyvars
               val env = envWithVars tyvars (mkEnv ())
             in
               valDec (Pat.Const tycon)
                 (tyVarFnExp tyvars (singleLetExp genericDec
                    (genTy env false ty)))
             end) elems
    in
      multDec decs
    end

  fun genSimpleDatabind (env, ty, vars, data) =
    valDec (identPat ty) (tyVarFnExp vars (singleLetExp genericDec (genConstrs
      (envWithVars vars env, data))))

  fun genRecursiveDatabind (env, tycons, tys, vars) =
    let
      val yTok = mkToken "Y"
      val yDec = valDec (Pat.Const yTok) (Const (mkToken "Generic.Y"))
      val varExps = List.map Ty.Var vars
      val patToks =
        case vars of
          [] => tycons
        | _ => List.map #1 (generatedFixesAndArgs env)
      val fullPat = destructInfixLPat andTok (List.map identPat patToks)
      val exp =
        case vars of
          [] =>
            let
              val env = envWithVars vars env
              val exps =
                List.map
                  (fn tycon =>
                     let
                       val tycon = Token.toString tycon
                       val substMap = buildSubstMap env tycon varExps
                       val constrs = List.map (substConstr substMap)
                         (tyconConstrs env (Atom.atom tycon))
                     in
                       genConstrs (env, constrs)
                     end) tycons
            in
              singleLetExp genericDec (infixLExp andTok exps)
            end
        | _ =>
            let
              val dups: IntRedBlackSet.set AtomTable.hash_table =
                AtomTable.mkTable (100, LibBase.NotFound)
              val decs =
                List.map
                  (fn (tycon, ty) =>
                     let
                       val tyconA = Atom.atom (Token.toString tycon)
                       val args =
                         List.map
                           (fn Ty.Con {id, ...} => MaybeLongToken.getToken id
                             | Ty.Var v => mkTyVar v
                             | _ => raise Fail "Invalid arg")
                           (generatedArgsForTy env ty)
                       val argDups = findDuplicates args
                       val () = AtomTable.insert dups (tyconA, argDups)
                       val substMap =
                         buildSubstMap env (Token.toString tycon) varExps
                       val constrs = List.map (substConstr substMap)
                         (tyconConstrs env tyconA)
                     in
                       singleFunDec tycon
                         [destructTuplePat
                            (applyDuplicates (argDups, Pat.Const, args))]
                         (genConstrs (env, constrs))
                     end) (ListPair.zip (tycons, tys))
              val exps =
                List.map
                  (fn (tycon, args) =>
                     let
                       val tycon = baseTyName (Token.toString tycon)
                       val argDups = AtomTable.lookup dups (Atom.atom tycon)
                       val tycon = mkToken tycon
                     in
                       case applyDuplicates (argDups, genTy env false, args) of
                         [] => Const tycon
                       | args => appExp [Const tycon, tupleExp args]
                     end) (generatedFixesAndArgs env)
            in
              singleLetExp (multDec (genericDec :: decs))
                (infixLExp andTok exps)
            end
      val lam = singleFnExp fullPat exp
      val ys =
        let
          val ys = List.tabulate (List.length patToks, fn _ => Const yTok)
        in
          (if List.length ys = 1 then fn e => e else parensExp)
            (infixLExp prodTok ys)
        end
      fun header exp =
        case vars of
          [] => valDec fullPat (singleLetExp (multDec [tieDec, yDec]) exp)
        | _ =>
            let
              val concatTys = mkToken (String.concatWith "_"
                (List.map Token.toString tycons))
              fun unpackingDecs _ [] = []
                | unpackingDecs i (ty :: tys) =
                    valDec (Pat.Const ty) (singleFnExp (Pat.Const quesTok) (App
                      { left = Const (mkToken ("#" ^ Int.toString i))
                      , right = parensExp
                          (App {left = Const concatTys, right = Const quesTok})
                      })) :: unpackingDecs (i + 1) tys
              val tyToks =
                List.map (Option.valOf o generatedFixNameForTy env) tys
              val tyFixes = List.map Const tyToks
              val hiddenPat = destructInfixLPat andTok
                (List.map
                   (fn tok =>
                      if List.exists (fn t => Token.same (tok, t)) tyToks then
                        identPat tok
                      else
                        wildPat) patToks)
            in
              multDec
                (valDec (Pat.Const concatTys) (tyVarFnExp vars
                   (singleLetExp (multDec [tieDec, yDec, valDec hiddenPat exp])
                      (tupleExp tyFixes))) :: unpackingDecs 1 tycons)
            end
    in
      header (appExp [Const (mkToken "fix"), ys, parensExp lam])
    end

  val genDatabind = genDatabindHelper (genSimpleDatabind, genRecursiveDatabind)

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
