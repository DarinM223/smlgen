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
  open BuildAst Utils
  structure SCC =
    GraphSCCFn (struct type ord_key = int val compare = Int.compare end)
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

  fun subst map ty =
    case ty of
      Ty.Var tok =>
        (AtomMap.lookup (map, Atom.atom (Token.toString tok))
         handle LibBase.NotFound => ty)
    | Ty.Record {left, elems, delims, right} =>
        let
          val elems = ArraySlice.foldr (op::) [] elems
          val elems =
            List.map
              (fn {colon, lab, ty} =>
                 {colon = colon, lab = lab, ty = subst map ty}) elems
          val elems = ArraySlice.full (Array.fromList elems)
        in
          Ty.Record {left = left, elems = elems, delims = delims, right = right}
        end
    | Ty.Tuple {elems, delims} =>
        let
          val elems = ArraySlice.foldr (op::) [] elems
          val elems = List.map (subst map) elems
          val elems = ArraySlice.full (Array.fromList elems)
        in
          Ty.Tuple {elems = elems, delims = delims}
        end
    | Ty.Con {args, id} =>
        let
          val args =
            case args of
              SyntaxSeq.Empty => SyntaxSeq.Empty
            | SyntaxSeq.One t => SyntaxSeq.One (subst map t)
            | SyntaxSeq.Many {delims, elems, left, right} =>
                let
                  val elems = ArraySlice.foldr (op::) [] elems
                  val elems = List.map (subst map) elems
                  val elems = ArraySlice.full (Array.fromList elems)
                in
                  SyntaxSeq.Many
                    {delims = delims, elems = elems, left = left, right = right}
                end
        in
          Ty.Con {args = args, id = id}
        end
    | Ty.Arrow {from, arrow, to} =>
        Ty.Arrow {from = subst map from, arrow = arrow, to = subst map to}
    | Ty.Parens {left, ty, right} =>
        Ty.Parens {left = left, ty = subst map ty, right = right}

  fun substConstr substMap {arg = SOME {ty, off}, id, opp} =
        {arg = SOME {ty = subst substMap ty, off = off}, id = id, opp = opp}
    | substConstr _ c = c

  type env =
    { resultTable: Token.token AtomTable.hash_table
    , resultLinks: Ty.ty list AtomTable.hash_table
    , vars: Token.token list
    , tyTokToId: int AtomTable.hash_table
    , tyData: (Token.token * Token.token SyntaxSeq.t * constr list) IntHashTable.hash_table
    , c: int ref
    }
  exception Beta
  fun mkEnv () : env =
    { resultTable = AtomTable.mkTable (100, Beta)
    , resultLinks = AtomTable.mkTable (100, Beta)
    , vars = []
    , tyTokToId = AtomTable.mkTable (100, Beta)
    , tyData = IntHashTable.mkTable (100, Beta)
    , c = ref 0
    }
  fun envWithVars vars
    ({resultTable, resultLinks, tyTokToId, tyData, c, ...}: env) : env =
    ( AtomTable.clear resultTable
    ; AtomTable.clear resultLinks
    ; { resultTable = resultTable
      , resultLinks = resultLinks
      , vars = vars
      , tyTokToId = tyTokToId
      , tyData = tyData
      , c = c
      }
    )
  fun addResultLink (env: env) k v =
    let val s = AtomTable.lookup (#resultLinks env) k handle Beta => []
    in AtomTable.insert (#resultLinks env) (k, v :: s)
    end

  fun buildSubstMap (env: env) tycon tys =
    let
      val i = AtomTable.lookup (#tyTokToId env) (Atom.atom tycon)
      val (_, vars, _) = IntHashTable.lookup (#tyData env) i
    in
      List.foldl
        (fn ((var, ty), acc) =>
           AtomMap.insert (acc, Atom.atom (Token.toString var), ty))
        AtomMap.empty (ListPair.zip (syntaxSeqToList vars, tys))
    end

  fun tyconToTy (env: env, tycon) =
    let
      val i = AtomTable.lookup (#tyTokToId env) (Atom.atom tycon)
      val (_, vars, _) = IntHashTable.lookup (#tyData env) i
    in
      Ty.Con
        { args = syntaxSeqMap Ty.Var vars
        , id = MaybeLongToken.make (mkToken tycon)
        }
    end

  fun traverseTy (env: env, tycon, substMap) : unit =
    let
      val i = AtomTable.lookup (#tyTokToId env) (Atom.atom tycon)
      val (_, vars, constrs) = IntHashTable.lookup (#tyData env) i
      val ty = subst substMap (tyconToTy (env, tycon))
      val constrs = List.map (substConstr substMap) constrs
      val tyStrA = Atom.atom (showTy ty)
    in
      if AtomTable.inDomain (#resultTable env) tyStrA then
        ()
      else
        let
          val () = List.app (addResultLink env tyStrA)
            (List.map
               (fn s => AtomMap.lookup (substMap, Atom.atom (Token.toString s)))
               (syntaxSeqToList vars))
          val i = !(#c env) before (#c env := !(#c env) + 1)
          val freshTycon = mkToken (tycon ^ "_" ^ Int.toString i)
          val () = AtomTable.insert (#resultTable env) (tyStrA, freshTycon)

          fun go (Ty.Var _) = ()
            | go (Ty.Record {elems, ...}) =
                ArraySlice.app (fn {ty, ...} => go ty) elems
            | go (Ty.Tuple {elems, ...}) = ArraySlice.app go elems
            | go (ty as Ty.Con {args, id}) =
                let
                  val tys = syntaxSeqToList args
                  val tycon' = Token.toString
                    (stripToken (MaybeLongToken.getToken id))
                in
                  if AtomTable.inDomain (#tyTokToId env) (Atom.atom tycon') then
                    ( traverseTy (env, tycon', buildSubstMap env tycon' tys)
                    ; addResultLink env tyStrA (Ty.Con
                        { args = SyntaxSeq.Empty
                        , id =
                            MaybeLongToken.make
                              (AtomTable.lookup (#resultTable env)
                                 (Atom.atom (showTy ty)))
                        })
                    )
                  else
                    List.app go tys
                end
            | go (Ty.Arrow {from, to, ...}) =
                (go from; go to)
            | go (Ty.Parens {ty, ...}) = go ty
        in
          List.app (fn {arg = SOME {ty, ...}, ...} => go ty | _ => ()) constrs
        end
    end

  fun genTy (env: env) parens ty =
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
            case AtomTable.find (#resultTable env) (Atom.atom (showTy ty)) of
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

  fun findDuplicates links =
    let
      fun go (_, _, build, []) = build
        | go (i, set, build, l :: ls) =
            let
              val lA = Atom.atom (Token.toString l)
              val build =
                if AtomSet.member (set, lA) then IntRedBlackSet.add (build, i)
                else build
            in
              go (i + 1, AtomSet.add (set, lA), build, ls)
            end
    in
      go (0, AtomSet.empty, IntRedBlackSet.empty, links)
    end

  fun applyDuplicates (dupSet, f, l) =
    let
      fun go (i, e :: es) =
            if IntRedBlackSet.member (dupSet, i) then go (i + 1, es)
            else f e :: go (i + 1, es)
        | go (_, []) = []
    in
      go (0, l)
    end

  fun genSimpleDatabind (env: env, i) =
    let
      val (ty, vars, data) = IntHashTable.lookup (#tyData env) i
      val env = envWithVars (syntaxSeqToList vars) env
    in
      valDec (identPat ty) (tyVarFnExp (#vars env) (singleLetExp genericDec
        (genConstrs (env, data))))
    end

  fun genRecursiveDatabind (env: env, is) =
    let
      val datas = List.map (IntHashTable.lookup (#tyData env)) is
      val tys = List.map #1 datas
      fun maxList maxLen max (l :: ls) =
            let val len = List.length l
            in if len > maxLen then maxList len l ls else maxList maxLen max ls
            end
        | maxList _ max [] = max
      val varLists = List.map (syntaxSeqToList o #2) datas
      val vars = maxList 0 [] varLists
      val varExps = List.map Ty.Var vars
      val env = envWithVars vars env
      val startTys =
        List.map
          (fn tycon =>
             let val tycon = Token.toString tycon
             in subst (buildSubstMap env tycon varExps) (tyconToTy (env, tycon))
             end) tys
      val yTok = mkToken "Y"
      val yDec = valDec (Pat.Const yTok) (Const (mkToken "Generic.Y"))
      val () =
        List.app
          (fn tycon =>
             let
               val tycon = Token.toString tycon
               val substMap = buildSubstMap env tycon varExps
             in
               traverseTy (env, tycon, substMap)
             end) tys
      val patToks =
        case vars of
          [] => tys
        | _ => AtomTable.listItems (#resultTable env)
      val fullPat = destructInfixLPat andTok (List.map identPat patToks)
      fun linksToToks links =
        List.map
          (fn Ty.Con {id, ...} => MaybeLongToken.getToken id
            | Ty.Var v => mkTyVar v
            | _ => raise Fail "Invalid link") links
      val exp =
        case vars of
          [] =>
            let
              val env = envWithVars vars env
              val exps =
                List.map
                  (fn (tycon, _, constrs) =>
                     let
                       val substMap =
                         buildSubstMap env (Token.toString tycon) varExps
                       val constrs = List.map (substConstr substMap) constrs
                     in
                       genConstrs (env, constrs)
                     end) datas
            in
              singleLetExp genericDec (infixLExp andTok exps)
            end
        | _ =>
            let
              val dups: IntRedBlackSet.set AtomTable.hash_table =
                AtomTable.mkTable (100, Beta)
              val decs =
                List.map
                  (fn (tycon, ty) =>
                     let
                       val tyconA = Atom.atom (Token.toString tycon)
                       val links = AtomTable.lookup (#resultLinks env)
                         (Atom.atom (showTy ty))
                       val links = linksToToks links
                       val linkDups = findDuplicates links
                       val () = AtomTable.insert dups (tyconA, linkDups)
                       val i = AtomTable.lookup (#tyTokToId env) tyconA
                       val (_, _, constrs) = IntHashTable.lookup (#tyData env) i
                       val substMap =
                         buildSubstMap env (Token.toString tycon) varExps
                       val constrs = List.map (substConstr substMap) constrs
                     in
                       singleFunDec tycon
                         [destructTuplePat
                            (applyDuplicates (linkDups, Pat.Const, links))]
                         (genConstrs (env, constrs))
                     end) (ListPair.zip (tys, startTys))
              val exps =
                List.map
                  (fn (a, links) =>
                     let
                       val fixTycon = Token.toString
                         (AtomTable.lookup (#resultTable env) a)
                       val (tycon, _) =
                         Substring.splitr (fn ch => ch <> #"_")
                           (Substring.full fixTycon)
                       val tycon = Substring.string (Substring.trimr 1 tycon)
                       val linkDups = AtomTable.lookup dups (Atom.atom tycon)
                       val tycon = mkToken tycon
                       val links = applyDuplicates
                         (linkDups, genTy env false, links)
                     in
                       case links of
                         [] => Const tycon
                       | _ => appExp [Const tycon, tupleExp links]
                     end) (AtomTable.listItemsi (#resultLinks env))
            in
              singleLetExp (multDec (genericDec :: decs))
                (infixLExp andTok exps)
            end
      val lam = singleFnExp fullPat exp
      val ys =
        let
          val ys =
            List.tabulate
              ( case vars of
                  [] => List.length tys
                | _ => AtomTable.numItems (#resultTable env)
              , fn _ => Const yTok
              )
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
                (List.map Token.toString tys))
              fun unpackingDecs _ [] = []
                | unpackingDecs i (ty :: tys) =
                    valDec (Pat.Const ty) (singleFnExp (Pat.Const quesTok) (App
                      { left = Const (mkToken ("#" ^ Int.toString i))
                      , right = parensExp
                          (App {left = Const concatTys, right = Const quesTok})
                      })) :: unpackingDecs (i + 1) tys
              val startTyToks =
                List.map
                  (AtomTable.lookup (#resultTable env) o Atom.atom o showTy)
                  startTys
              val startTyFixes = List.map Const startTyToks
              val hiddenPat = destructInfixLPat andTok
                (List.map
                   (fn tok =>
                      if List.exists (fn t => Token.same (tok, t)) startTyToks then
                        identPat tok
                      else
                        wildPat) patToks)
            in
              multDec
                (valDec (Pat.Const concatTys) (tyVarFnExp vars
                   (singleLetExp (multDec [tieDec, yDec, valDec hiddenPat exp])
                      (tupleExp startTyFixes))) :: unpackingDecs 1 tys)
            end
    in
      header (appExp [Const (mkToken "fix"), ys, parensExp lam])
    end

  fun genDatabind ({elems, ...}: datbind) =
    let
      val elems = ArraySlice.foldr (op::) [] elems
      val tys =
        List.map
          (fn {tycon, tyvars, elems, ...} =>
             (stripToken tycon, tyvars, ArraySlice.foldr (op::) [] elems)) elems
      val c = ref 0
      val env = mkEnv ()
      val tyLinks: IntListSet.set IntHashTable.hash_table =
        IntHashTable.mkTable (100, Beta)
      fun addLink i j =
        let val data = IntHashTable.lookup tyLinks i
        in IntHashTable.insert tyLinks (i, IntListSet.add (data, j))
        end
      fun buildLinks _ (Ty.Var _) = ()
        | buildLinks i (Ty.Record {elems, ...}) =
            ArraySlice.app (buildLinks i o #ty) elems
        | buildLinks i (Ty.Tuple {elems, ...}) =
            ArraySlice.app (buildLinks i) elems
        | buildLinks i (Ty.Con {id, args, ...}) =
            let
              val tok = Atom.atom (Token.toString (MaybeLongToken.getToken id))
            in
              case AtomTable.find (#tyTokToId env) tok of
                SOME j => addLink i j
              | NONE => ();
              case args of
                SyntaxSeq.Empty => ()
              | SyntaxSeq.One ty => buildLinks i ty
              | SyntaxSeq.Many {elems, ...} =>
                  ArraySlice.app (buildLinks i) elems
            end
        | buildLinks i (Ty.Arrow {from, to, ...}) =
            (buildLinks i from; buildLinks i to)
        | buildLinks i (Ty.Parens {ty, ...}) = buildLinks i ty
      val roots =
        List.map
          (fn (ty, vars, constrs) =>
             let
               val i = !c before c := !c + 1
               val () = AtomTable.insert (#tyTokToId env)
                 (Atom.atom (Token.toString ty), i)
               val () = IntHashTable.insert tyLinks (i, IntListSet.empty)
               val () =
                 IntHashTable.insert (#tyData env) (i, (ty, vars, constrs))
             in
               i
             end) tys
      val () =
        List.app
          (fn (i, (_, _, constrs)) =>
             List.app
               (fn {arg = SOME {ty, ...}, ...} => buildLinks i ty | _ => ())
               constrs) (ListPair.zip (roots, tys))
      val scc = SCC.topOrder'
        { roots = roots
        , follow = IntListSet.toList o IntHashTable.lookup tyLinks
        }
      fun handleComponent (SCC.SIMPLE i) = genSimpleDatabind (env, i)
        | handleComponent (SCC.RECURSIVE is) = genRecursiveDatabind (env, is)
    in
      multDec (List.map handleComponent (List.rev scc))
    end

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
