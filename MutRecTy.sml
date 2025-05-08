structure MutRecTy: MUT_REC_TY =
struct
  open Ast Ast.Exp TokenUtils Tokens BuildAst Utils

  structure SCC =
    GraphSCCFn (struct type ord_key = int val compare = Int.compare end)

  datatype type_data = Databind of constr list | Typebind of Ty.ty

  fun normalizeTypeData (Databind datbinds) =
        let
          fun normalizeArg {off, ty} = {off = off, ty = normalize ty}
          fun normalizeDatbind {arg, id, opp} =
            {arg = Option.map normalizeArg arg, id = id, opp = opp}
        in
          Databind (List.map normalizeDatbind datbinds)
        end
    | normalizeTypeData (Typebind ty) =
        Typebind (normalize ty)

  structure TyTable =
    HashTableFn
      (struct
         type hash_key = Ast.Ty.ty
         val hashVal = Ast.Ty.hash
         val sameKey = Ast.Ty.==
       end)

  datatype env =
    Env of
      { tyToFix: Token.token TyTable.hash_table
      , tyToArgs: Ty.ty list TyTable.hash_table
      , fixToTy: Ty.ty AtomTable.hash_table
      , vars: Token.token list
      , tyTokToId: int AtomTable.hash_table
      , tyData: (Token.token * Token.token SyntaxSeq.t * type_data) IntHashTable.hash_table
      , c: int ref
      }

  fun subst map ty =
    case ty of
      Ty.Var tok =>
        (AtomMap.lookup (map, Atom.atom (Token.toString tok))
         handle LibBase.NotFound => ty)
    | Ty.Record {left, elems, delims, right} =>
        let
          val substField = fn {colon, lab, ty} =>
            {colon = colon, lab = lab, ty = subst map ty}
          val elems = Seq.map substField elems
        in
          Ty.Record {left = left, elems = elems, delims = delims, right = right}
        end
    | Ty.Tuple {elems, delims} =>
        Ty.Tuple {elems = Seq.map (subst map) elems, delims = delims}
    | Ty.Con {args, id} =>
        let val args = syntaxSeqMapTy (subst map) args
        in Ty.Con {args = args, id = id}
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

  fun mkEnv tableSize =
    Env
      { tyToFix = TyTable.mkTable (tableSize, LibBase.NotFound)
      , tyToArgs = TyTable.mkTable (tableSize, LibBase.NotFound)
      , fixToTy = AtomTable.mkTable (tableSize, LibBase.NotFound)
      , vars = []
      , tyTokToId = AtomTable.mkTable (tableSize, LibBase.NotFound)
      , tyData = IntHashTable.mkTable (tableSize, LibBase.NotFound)
      , c = ref 0
      }

  fun envWithVars vars
    (Env {tyToFix, tyToArgs, fixToTy, tyTokToId, tyData, c, ...}) =
    ( TyTable.clear tyToFix
    ; TyTable.clear tyToArgs
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
    TyTable.insertWith (fn (v', v) => v @ v') tyToArgs (k, [v])

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
        { args = syntaxSeqMapTy Ty.Var vars
        , id = MaybeLongToken.make (mkToken tycon)
        }
    end

  exception RecursionLimit
  val maxTySizeErrorMsg = "Max type size limit exceeded\n"

  fun traverseTy
    (env as Env {c, tyTokToId, tyData, tyToFix, fixToTy, ...}, tycon, substMap) =
    let
      val i = AtomTable.lookup tyTokToId (Atom.atom tycon)
      val (_, vars, dat) = IntHashTable.lookup tyData i
      val ty0 = subst substMap (tyconToTy (env, tycon))
    in
      if TyTable.inDomain tyToFix ty0 then
        ()
      else
        let
          val () = List.app (addTyArg env ty0)
            (List.map
               (fn s => AtomMap.lookup (substMap, Atom.atom (Token.toString s)))
               (syntaxSeqToList vars))
          val i = !c before c := !c + 1
          val freshTycon = tycon ^ "_" ^ Int.toString i
          val () = TyTable.insert tyToFix (ty0, mkToken freshTycon)
          val () = AtomTable.insert fixToTy (Atom.atom freshTycon, ty0)

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
                      val () =
                        if tySize ty > ! Options.maxTySize then
                          raise RecursionLimit
                        else
                          ()
                      val con = fn () =>
                        Ty.Con
                          { args = Ast.SyntaxSeq.Empty
                          , id = MaybeLongToken.make (TyTable.lookup tyToFix ty)
                          }
                    in
                      traverseTy (env, tycon', buildSubstMap env tycon' tys);
                      addTyArg env ty0 (con ())
                    end
                  else
                    List.app go tys
                end
            | go (Ty.Arrow {from, to, ...}) =
                (go from; go to)
            | go (Ty.Parens {ty, ...}) = go ty
        in
          case dat of
            Databind constrs =>
              List.app (fn {arg = SOME {ty, ...}, ...} => go ty | _ => ())
                (List.map (substConstr substMap) constrs)
          | Typebind ty => go (subst substMap ty)
        end
    end

  fun generatedFixNameForTy (Env {tyToFix, ...}) = TyTable.find tyToFix
  fun generatedArgsForTy (Env {tyToArgs, ...}) = TyTable.lookup tyToArgs
  fun generatedFixesAndArgs (Env {tyToFix, tyToArgs, ...}) =
    List.map (fn (a, links) => (TyTable.lookup tyToFix a, links))
      (TyTable.listItemsi tyToArgs)

  fun tyconIsGeneratedFix (Env {fixToTy, ...}) tycon =
    AtomTable.inDomain fixToTy (Atom.atom tycon)

  fun tyconData (Env {tyTokToId, tyData, ...}) tyconAtom =
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
          fun unpackQuesFn f =
            if normalizedLen = 0 then
              f unitExp
            else
              case f (Const quesTok) of
                exp as App {left, right = Const quesTok'} =>
                  if Token.same (quesTok, quesTok') then left
                  else singleFnExp (Pat.Const quesTok) exp
              | exp => singleFnExp (Pat.Const quesTok) exp
        in
          if one then
            unpackQuesFn (fn exp => (appExp [Const tupledName, exp]))
          else if List.length vars = normalizedLen then
            unpackQuesFn (fn exp =>
              appExp [mkNum i, parensExp (appExp [Const tupledName, exp])])
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

  fun genDatabindHelper (genSimple, genRecursive) ({elems, ...}: datbind)
    (typbind: typbind option) =
    let
      val tys =
        List.map
          (fn {tycon, tyvars, elems, ...} =>
             (stripToken tycon, tyvars, Seq.toList elems)) (Seq.toList elems)
      val c = ref 0
      val env as Env {tyData, tyTokToId, ...} =
        mkEnv (! Options.defaultTableSize)
      val tyLinks: IntListSet.set IntHashTable.hash_table = IntHashTable.mkTable
        (List.length tys + Seq.length elems, LibBase.NotFound)
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
              ignore (syntaxSeqMap (buildLinks i) args)
            end
        | buildLinks i (Ty.Arrow {from, to, ...}) =
            (buildLinks i from; buildLinks i to)
        | buildLinks i (Ty.Parens {ty, ...}) = buildLinks i ty
      val dataRoots =
        List.map
          (fn (ty, vars, constrs) =>
             let
               val i = !c before c := !c + 1
               val () = AtomTable.insert tyTokToId
                 (Atom.atom (Token.toString ty), i)
               val () = IntHashTable.insert tyLinks (i, IntListSet.empty)
               val () = IntHashTable.insert tyData
                 (i, (ty, vars, normalizeTypeData (Databind constrs)))
             in
               i
             end) tys
      (* Initialize tyLinks and tyData for withtype types also *)
      val typeRoots =
        case typbind of
          SOME {elems, ...} =>
            List.map
              (fn {tycon, tyvars, ty, ...} =>
                 let
                   val i = !c before c := !c + 1
                   val () = AtomTable.insert tyTokToId
                     (Atom.atom (Token.toString tycon), i)
                   val () = IntHashTable.insert tyLinks (i, IntListSet.empty)
                   val () = IntHashTable.insert tyData
                     (i, (tycon, tyvars, normalizeTypeData (Typebind ty)))
                 in
                   i
                 end) (Seq.toList elems)
        | NONE => []
      val roots = dataRoots @ typeRoots
      val () =
        List.app
          (fn (i, (_, _, constrs)) =>
             List.app
               (fn {arg = SOME {ty, ...}, ...} => buildLinks i ty | _ => ())
               constrs) (ListPair.zip (dataRoots, tys))
      (* Build links for withtype types also *)
      val () =
        Option.app
          (fn {elems, ...} =>
             List.app (fn (i, {ty, ...}) => buildLinks i ty)
               (ListPair.zip (typeRoots, Seq.toList elems))) typbind
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
            handle RecursionLimit => (print maxTySizeErrorMsg; DecEmpty)
    in
      multDec (List.map handleComponent (List.rev scc))
    end
  fun genSingleTypebind genTypebind (tyTok, vars, ty) =
    let
      val elem =
        {eq = equalTok, tycon = tyTok, ty = ty, tyvars = listToSyntaxSeq vars}
      val bind: typbind = {elems = Seq.singleton elem, delims = Seq.empty ()}
    in
      genTypebind bind
    end
end
