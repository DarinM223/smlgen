structure MutRecTy: MUT_REC_TY =
struct
  open BuildAst Utils

  structure SCC =
    GraphSCCFn (struct type ord_key = int val compare = Int.compare end)

  datatype env =
    Env of
      { resultTable: Token.token AtomTable.hash_table
      , resultLinks: Ty.ty list AtomTable.hash_table
      , vars: Token.token list
      , tyTokToId: int AtomTable.hash_table
      , tyData: (Token.token * Token.token SyntaxSeq.t * constr list) IntHashTable.hash_table
      , c: int ref
      }

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

  fun mkEnv () =
    Env
      { resultTable = AtomTable.mkTable (100, LibBase.NotFound)
      , resultLinks = AtomTable.mkTable (100, LibBase.NotFound)
      , vars = []
      , tyTokToId = AtomTable.mkTable (100, LibBase.NotFound)
      , tyData = IntHashTable.mkTable (100, LibBase.NotFound)
      , c = ref 0
      }

  fun envWithVars vars
    (Env {resultTable, resultLinks, tyTokToId, tyData, c, ...}) =
    ( AtomTable.clear resultTable
    ; AtomTable.clear resultLinks
    ; Env
        { resultTable = resultTable
        , resultLinks = resultLinks
        , vars = vars
        , tyTokToId = tyTokToId
        , tyData = tyData
        , c = c
        }
    )

  fun addResultLink (Env {resultLinks, ...}) k v =
    let val s = AtomTable.lookup resultLinks k handle LibBase.NotFound => []
    in AtomTable.insert resultLinks (k, v :: s)
    end

  fun buildSubstMap (Env {tyTokToId, tyData, ...}) tycon tys =
    let
      val i = AtomTable.lookup tyTokToId (Atom.atom tycon)
      val (_, vars, _) = IntHashTable.lookup tyData i
    in
      List.foldl
        (fn ((var, ty), acc) =>
           AtomMap.insert (acc, Atom.atom (Token.toString var), ty))
        AtomMap.empty (ListPair.zip (syntaxSeqToList vars, tys))
    end

  fun tyconToTy (Env {tyTokToId, tyData, ...}, tycon) =
    let
      val i = AtomTable.lookup tyTokToId (Atom.atom tycon)
      val (_, vars, _) = IntHashTable.lookup tyData i
    in
      Ty.Con
        { args = syntaxSeqMap Ty.Var vars
        , id = MaybeLongToken.make (mkToken tycon)
        }
    end

  fun traverseTy
    (env as Env {c, tyTokToId, tyData, resultTable, ...}, tycon, substMap) =
    let
      val i = AtomTable.lookup tyTokToId (Atom.atom tycon)
      val (_, vars, constrs) = IntHashTable.lookup tyData i
      val ty = subst substMap (tyconToTy (env, tycon))
      val constrs = List.map (substConstr substMap) constrs
      val tyStrA = Atom.atom (showTy ty)
    in
      if AtomTable.inDomain resultTable tyStrA then
        ()
      else
        let
          val () = List.app (addResultLink env tyStrA)
            (List.map
               (fn s => AtomMap.lookup (substMap, Atom.atom (Token.toString s)))
               (syntaxSeqToList vars))
          val i = !c before c := !c + 1
          val freshTycon = mkToken (tycon ^ "_" ^ Int.toString i)
          val () = AtomTable.insert resultTable (tyStrA, freshTycon)

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
                  if AtomTable.inDomain tyTokToId (Atom.atom tycon') then
                    ( traverseTy (env, tycon', buildSubstMap env tycon' tys)
                    ; addResultLink env tyStrA (Ty.Con
                        { args = SyntaxSeq.Empty
                        , id = MaybeLongToken.make (AtomTable.lookup resultTable
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

  fun generatedFixNameForTy (Env {resultTable, ...}) ty =
    AtomTable.find resultTable (Atom.atom (showTy ty))

  fun generatedArgsForTy (Env {resultLinks, ...}) ty =
    AtomTable.lookup resultLinks (Atom.atom (showTy ty))

  fun generatedFixesAndArgs (Env {resultTable, resultLinks, ...}) =
    List.map (fn (a, links) => (AtomTable.lookup resultTable a, links))
      (AtomTable.listItemsi resultLinks)

  fun tyconConstrs (Env {tyTokToId, tyData, ...}) tyconAtom =
    let
      val i = AtomTable.lookup tyTokToId tyconAtom
      val (_, _, constrs) = IntHashTable.lookup tyData i
    in
      constrs
    end

  val baseTyName =
    Substring.string o Substring.trimr 1 o #1
    o Substring.splitr (fn ch => ch <> #"_") o Substring.full

  fun unpackingDecs (tyname, l) =
    let
      val one = List.length l = 1
      val mkNum = fn ? => Const (mkToken ("#" ^ Int.toString ?))
      fun unpack i ? =
        if one then ? else appExp [mkNum i, parensExp ?]
      fun go _ [] = []
        | go i (ty :: tys) =
            valDec (Pat.Const ty) (singleFnExp (Pat.Const quesTok) (unpack i
              (appExp [Const tyname, Const quesTok]))) :: go (i + 1) tys
    in
      go 1 l
    end

  fun genDatabindHelper (genSimple, genRecursive) ({elems, ...}: datbind) =
    let
      val elems = ArraySlice.foldr (op::) [] elems
      val tys =
        List.map
          (fn {tycon, tyvars, elems, ...} =>
             (stripToken tycon, tyvars, ArraySlice.foldr (op::) [] elems)) elems
      val c = ref 0
      val env as Env {tyData, tyTokToId, ...} = mkEnv ()
      val tyLinks: IntListSet.set IntHashTable.hash_table =
        IntHashTable.mkTable (100, LibBase.NotFound)
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
              case AtomTable.find tyTokToId tok of
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
               val () = AtomTable.insert tyTokToId
                 (Atom.atom (Token.toString ty), i)
               val () = IntHashTable.insert tyLinks (i, IntListSet.empty)
               val () = IntHashTable.insert tyData (i, (ty, vars, constrs))
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
      fun handleComponent (SCC.SIMPLE i) =
            let val (ty, vars, data) = IntHashTable.lookup tyData i
            in genSimple (env, ty, syntaxSeqToList vars, data)
            end
        | handleComponent (SCC.RECURSIVE is) =
            let
              val datas = List.map (IntHashTable.lookup tyData) is
              val tycons = List.map #1 datas
              val tycons' = List.map Token.toString tycons
              fun maxList maxLen max (l :: ls) =
                    let
                      val len = List.length l
                    in
                      if len > maxLen then maxList len l ls
                      else maxList maxLen max ls
                    end
                | maxList _ max [] = max
              val vars = maxList 0 [] (List.map (syntaxSeqToList o #2) datas)
              val varExps = List.map Ty.Var vars
              val env = envWithVars vars env
              val tys =
                List.map
                  (fn tycon =>
                     subst (buildSubstMap env tycon varExps)
                       (tyconToTy (env, tycon))) tycons'
              val () =
                List.app
                  (fn tycon =>
                     let val substMap = buildSubstMap env tycon varExps
                     in traverseTy (env, tycon, substMap)
                     end) tycons'
            in
              genRecursive (env, tycons, tys, vars)
            end
    in
      multDec (List.map handleComponent (List.rev scc))
    end
end
