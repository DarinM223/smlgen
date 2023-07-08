structure MutRecTy: MUT_REC_TY =
struct
  open BuildAst Utils

  structure SCC =
    GraphSCCFn (struct type ord_key = int val compare = Int.compare end)

  datatype env =
    Env of
      { tyToFix: Token.token AtomTable.hash_table
      , tyToArgs: Ty.ty list AtomTable.hash_table
      , fixToTy: Ty.ty AtomTable.hash_table
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
      { tyToFix = AtomTable.mkTable (100, LibBase.NotFound)
      , tyToArgs = AtomTable.mkTable (100, LibBase.NotFound)
      , fixToTy = AtomTable.mkTable (100, LibBase.NotFound)
      , vars = []
      , tyTokToId = AtomTable.mkTable (100, LibBase.NotFound)
      , tyData = IntHashTable.mkTable (100, LibBase.NotFound)
      , c = ref 0
      }

  fun envWithVars vars
    (Env {tyToFix, tyToArgs, fixToTy, tyTokToId, tyData, c, ...}) =
    ( AtomTable.clear tyToFix
    ; AtomTable.clear tyToArgs
    ; AtomTable.clear fixToTy
    ; Env
        { tyToFix = tyToFix
        , tyToArgs = tyToArgs
        , fixToTy = fixToTy
        , vars = vars
        , tyTokToId = tyTokToId
        , tyData = tyData
        , c = c
        }
    )

  fun addTyArg (Env {tyToArgs, ...}) k v =
    let val s = AtomTable.lookup tyToArgs k handle LibBase.NotFound => []
    in AtomTable.insert tyToArgs (k, v :: s)
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

  exception RecursionLimit
  val maxTySize = ref 5000

  fun traverseTy
    (env as Env {c, tyTokToId, tyData, tyToFix, fixToTy, ...}, tycon, substMap) =
    let
      val i = AtomTable.lookup tyTokToId (Atom.atom tycon)
      val (_, vars, constrs) = IntHashTable.lookup tyData i
      val ty = subst substMap (tyconToTy (env, tycon))
      val constrs = List.map (substConstr substMap) constrs
      val tyStrA = Atom.atom (showTy ty)
    in
      if AtomTable.inDomain tyToFix tyStrA then
        ()
      else
        let
          val () = List.app (addTyArg env tyStrA)
            (List.map
               (fn s => AtomMap.lookup (substMap, Atom.atom (Token.toString s)))
               (syntaxSeqToList vars))
          val i = !c before c := !c + 1
          val freshTycon = tycon ^ "_" ^ Int.toString i
          val () = AtomTable.insert tyToFix (tyStrA, mkToken freshTycon)
          val () = AtomTable.insert fixToTy (Atom.atom freshTycon, ty)

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
                    let
                      val tyStr = showTy ty
                      (* TODO: Use more accurate method to count "size" of type. *)
                      val () =
                        if String.size tyStr > !maxTySize then
                          raise RecursionLimit
                        else
                          ()
                      val con = fn () =>
                        Ty.Con
                          { args = Ast.SyntaxSeq.Empty
                          , id = MaybeLongToken.make
                              (AtomTable.lookup tyToFix (Atom.atom tyStr))
                          }
                    in
                      traverseTy (env, tycon', buildSubstMap env tycon' tys);
                      addTyArg env tyStrA (con ())
                    end
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

  fun generatedFixNameForTy (Env {tyToFix, ...}) ty =
    AtomTable.find tyToFix (Atom.atom (showTy ty))

  fun generatedArgsForTy (Env {tyToArgs, ...}) ty =
    AtomTable.lookup tyToArgs (Atom.atom (showTy ty))

  fun generatedFixesAndArgs (Env {tyToFix, tyToArgs, ...}) =
    List.map (fn (a, links) => (AtomTable.lookup tyToFix a, links))
      (AtomTable.listItemsi tyToArgs)

  fun tyconIsGeneratedFix (Env {fixToTy, ...}) tycon =
    AtomTable.inDomain fixToTy (Atom.atom tycon)

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

  fun unpackingDecs
    ( Env {tyTokToId, tyData, ...}
    , normalizedVars
    , tupledName
    , tyNames
    , toDec
    , default
    ) =
    let
      val one = List.length tyNames = 1
      val mkNum = fn ? => Const (mkToken ("#" ^ Int.toString ?))
      val normalizedLen = List.length normalizedVars
      fun padList ([], i, pad) =
            if i > 0 then pad :: padList ([], i - 1, pad) else []
        | padList (h :: t, i, pad) =
            h :: padList (t, i, pad)
      fun unpack (vars, i) =
        let
          val vars = List.map mkTyVar vars
          val defaultVar =
            case vars of
              v :: _ => v
            | _ => mkToken default
        in
          if one then
            singleFnExp (Pat.Const quesTok)
              (appExp [Const tupledName, Const quesTok])
          else if List.length vars = normalizedLen then
            singleFnExp (Pat.Const quesTok) (appExp
              [mkNum i, parensExp (appExp [Const tupledName, Const quesTok])])
          else
            let
              val tuple = tupleExp (List.map Const (padList
                (vars, normalizedLen - List.length vars, defaultVar)))
              val exp = appExp
                [mkNum i, parensExp (appExp [Const tupledName, tuple])]
            in
              case vars of
                [] => exp
              | _ =>
                  singleFnExp (destructTuplePat (List.map Pat.Const vars)) exp
            end
        end
      fun go (_, []) = []
        | go (i, tyName :: tyNames) =
            let
              val vars =
                (syntaxSeqToList o #2 o IntHashTable.lookup tyData
                 o AtomTable.lookup tyTokToId o Atom.atom o Token.toString)
                  tyName
                handle LibBase.NotFound => normalizedVars
            in
              valDec (Pat.Const (toDec tyName)) (unpack (vars, i))
              :: go (i + 1, tyNames)
            end
    in
      go (1, tyNames)
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
            handle RecursionLimit =>
              (print "Max type size limit exceeded\n"; DecEmpty)
    in
      multDec (List.map handleComponent (List.rev scc))
    end
end
