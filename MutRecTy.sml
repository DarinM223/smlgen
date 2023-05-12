structure MutRecTy =
struct
  open BuildAst Utils

  exception Beta
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
      { resultTable = AtomTable.mkTable (100, Beta)
      , resultLinks = AtomTable.mkTable (100, Beta)
      , vars = []
      , tyTokToId = AtomTable.mkTable (100, Beta)
      , tyData = IntHashTable.mkTable (100, Beta)
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
    let val s = AtomTable.lookup resultLinks k handle Beta => []
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
end
