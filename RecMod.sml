structure GatherTypes :> GATHER_TYPES =
struct
  fun visitor {c, typenameToBind} =
    { state = []
    , goDecType = fn (_, dec, _) => dec
    , goDecDatatype =
        fn ( path
           , dec
           , datbind as {elems, ...}: Ast.Exp.datbind
           , _: AstVisitor.withtypee
           ) =>
          let
            val types =
              Seq.map
                (String.concatWith "." o List.rev o (fn tycon => tycon :: path)
                 o Token.toString o #tycon) elems
            val datbindId = !c before c := !c + 1
          in (* TODO: rewrite datbind with withtypees *)
            ArraySlice.app
              (fn typ =>
                 AtomTable.insert typenameToBind
                   (Atom.atom typ, (datbindId, datbind))) types;
            dec
          end
    , onStructure = fn strid => fn path => Token.toString strid :: path
    , onFunctor = fn funid => fn path => Token.toString funid :: path
    }

  fun run (Ast.Ast topdecs : Ast.t) =
    let
      val typenameToBind: (int * Ast.Exp.datbind) AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
    in
      Seq.map
        (fn {topdec, semicolon} =>
           { topdec =
               AstVisitor.goTopDec
                 (visitor {typenameToBind = typenameToBind, c = ref 0}) topdec
           , semicolon = semicolon
           }) topdecs;
      typenameToBind
    end
end

structure RecMod :> RECURSIVE_MODULES =
struct
  structure AtomSCC =
    GraphSCCFn (struct type ord_key = Atom.atom val compare = Atom.compare end)

  fun addLinks (followTable, typename, datbind) =
    let
      open Ast Utils
      fun go (Ty.Var _) = ()
        | go (Ty.Record {elems, ...}) =
            ArraySlice.app (go o #ty) elems
        | go (Ty.Tuple {elems, ...}) = ArraySlice.app go elems
        | go (Ty.Con {id, args, ...}) =
            let
              val id = Token.toString (MaybeLongToken.getToken id)
              val idAtom = Atom.atom id
              val qualifiedIdAtom = Atom.atom
                (Utils.qualifiedTypePart (Atom.toString typename) ^ id)
            in
              (* Check if the type constructor is in the same structure first *)
              if AtomTable.inDomain followTable qualifiedIdAtom then
                AtomTable.insert followTable (typename, AtomSet.add
                  (AtomTable.lookup followTable typename, qualifiedIdAtom))
              else if AtomTable.inDomain followTable idAtom then
                AtomTable.insert followTable (typename, AtomSet.add
                  (AtomTable.lookup followTable typename, idAtom))
              else
                ();
              ignore (syntaxSeqMap go args)
            end
        | go (Ty.Arrow {from, to, ...}) =
            (go from; go to)
        | go (Ty.Parens {ty, ...}) = go ty
    in
      List.app go (datbindTys datbind)
    end

  type 'a track =
    {trackTypename: Token.token -> 'a, trackConstructor: Token.token -> 'a}

  val emptyTrack: 'a track =
    { trackTypename = fn _ => raise LibBase.NotFound
    , trackConstructor = fn _ => raise LibBase.NotFound
    }

  fun combineTracks (a: 'a track) (b: 'a track) : 'a track =
    { trackTypename = fn t => #trackTypename a t handle _ => #trackTypename b t
    , trackConstructor = fn t => #trackConstructor a t
                                 handle _ => #trackConstructor b t
    }

  (* For every datatype in the component,
     track how many times the typename and the constructor name appear.
  *)
  fun countTypesAndConstructors (component: Ast.Exp.datbind list) =
    let
      val typenameCount: int AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
      val constrCount: int AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
      fun incr (table, atom) =
        if AtomTable.inDomain table atom then
          AtomTable.insert table (atom, AtomTable.lookup table atom + 1)
        else
          AtomTable.insert table (atom, 1)
    in
      List.app
        (fn {elems, ...} =>
           ArraySlice.app
             (fn {tycon, elems, ...} =>
                ( incr (typenameCount, Atom.atom (Token.toString tycon))
                ; ArraySlice.app
                    (fn {id, ...} =>
                       incr (constrCount, Atom.atom (Token.toString id))) elems
                )) elems) component;
      { trackTypename =
          AtomTable.lookup typenameCount o Atom.atom o Token.toString
      , trackConstructor =
          AtomTable.lookup constrCount o Atom.atom o Token.toString
      }
    end

  val serialize = String.map (fn #"." => #"_" | ch => ch)

  fun componentSubstMap ({trackTypename, trackConstructor}: int track)
    (component: (string * int * Ast.Exp.datbind) list) =
    let
      val typenameRename: string AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
      val constrRename: string AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
    in
      List.app
        (fn (typename, _, {elems, ...}) =>
           ArraySlice.app
             (fn {tycon, elems, ...} =>
                let
                  val qualifiedTycon =
                    Utils.qualifiedTypePart typename ^ Token.toString tycon
                in
                  if trackTypename tycon > 1 then
                    AtomTable.insert typenameRename
                      (Atom.atom qualifiedTycon, serialize qualifiedTycon)
                  else
                    AtomTable.insert typenameRename
                      ( Atom.atom qualifiedTycon
                      , Utils.typenameTypePart qualifiedTycon
                      );
                  ArraySlice.app
                    (fn {id, ...} =>
                       if trackConstructor id > 1 then
                         AtomTable.insert constrRename
                           ( Atom.atom
                               (qualifiedTycon ^ "." ^ Token.toString id)
                           , serialize
                               (qualifiedTycon ^ "." ^ Token.toString id)
                           )
                       else
                         ()) elems
                end) elems) component;
      { trackTypename =
          Utils.mkToken o AtomTable.lookup typenameRename o Atom.atom
          o Token.toString
      , trackConstructor =
          Utils.mkToken o AtomTable.lookup constrRename o Atom.atom
          o Token.toString
      }
    end

  fun substDatbind ({trackTypename, trackConstructor}: Token.token track)
    (qualifiedPart: string) ({elems, delims}: Ast.Exp.datbind) =
    let
      open Ast Utils MaybeLongToken
      fun goTy (Ty.Var var) = Ty.Var var
        | goTy (Ty.Record {left, elems, delims, right}) =
            Ty.Record
              { left = left
              , elems =
                  Seq.map
                    (fn {lab, colon, ty} =>
                       {lab = lab, colon = colon, ty = goTy ty}) elems
              , delims = delims
              , right = right
              }
        | goTy (Ty.Tuple {elems, delims}) =
            Ty.Tuple {elems = Seq.map goTy elems, delims = delims}
        | goTy (Ty.Con {args, id}) =
            Ty.Con
              { args = syntaxSeqMap goTy args
              , id = make (trackTypename (getToken id)) handle _ => id
              }
        | goTy (Ty.Arrow {from, arrow, to}) =
            Ty.Arrow {from = goTy from, arrow = arrow, to = goTy to}
        | goTy (Ty.Parens {left, ty, right}) =
            Ty.Parens {left = left, ty = goTy ty, right = right}
      fun goConstr qualifiedTycon {opp, id, arg} =
        { opp = opp
        , id =
            trackConstructor (mkToken
              (qualifiedTycon ^ "." ^ Token.toString id))
            handle _ => id
        , arg = Option.map (fn {off, ty} => {off = off, ty = goTy ty}) arg
        }
      fun goTycon {tyvars, tycon, eq, elems, delims, optbar} =
        let
          val qualifiedTycon = qualifiedPart ^ Token.toString tycon
        in
          { tyvars = tyvars
          , tycon = trackTypename (mkToken qualifiedTycon) handle _ => tycon
          , eq = eq
          , elems = Seq.map (goConstr qualifiedTycon) elems
          , delims = delims
          , optbar = optbar
          }
        end
    in
      {elems = Seq.map goTycon elems, delims = delims}
    end

  val removeDuplicateDatbinds =
    let
      fun go seen ((s: string, i, datbind: Ast.Exp.datbind) :: rest) =
            if IntRedBlackSet.member (seen, i) then go seen rest
            else (s, i, datbind) :: go (IntRedBlackSet.add (seen, i)) rest
        | go _ [] = []
    in
      go IntRedBlackSet.empty
    end

  val traceFollowTable = AtomTable.appi (fn (a, b) =>
    ( print (Atom.toString a)
    ; print " -> ["
    ; AtomSet.app (fn c => (print (Atom.toString c); print ",")) b
    ; print "]\n"
    ))

  (*
  1. Track structure levels in environment.
     First pass: For every datatype, make a hashtable from full name (including structures) to a
     tuple of databind id (uniquely generated for every datatype in the topdec) and databind.
  2. For every datatype in the map, put links to other datatypes into another hashtable.
  3. Calculate the SCCs of the datatypes to find the connected datatype components.
  4. For each component, generate a merged structure name at the beginning and merge the datatypes
     into a single mutually recursive datatype.
  5. Rewrite the original structures to unpack the corresponding type in the recursive datatype.

  TODO: handle type aliases
  *)
  fun gen (Ast.Ast topdecs) =
    let
      val typenameToBind = GatherTypes.run (Ast.Ast topdecs)
      val followTable: AtomSet.set AtomTable.hash_table =
        AtomTable.mkTable (AtomTable.numItems typenameToBind, LibBase.NotFound)
      val () =
        AtomTable.appi
          (fn (typename, _) =>
             AtomTable.insert followTable (typename, AtomSet.empty))
          typenameToBind
      val () =
        AtomTable.appi
          (fn (typename, (_, datbind)) =>
             addLinks (followTable, typename, datbind)) typenameToBind
      val () = traceFollowTable followTable
      val roots = List.map #1 (AtomTable.listItemsi followTable)
      val components = AtomSCC.topOrder'
        {roots = roots, follow = AtomSet.toList o AtomTable.lookup followTable}
      val components =
        List.mapPartial
          (fn AtomSCC.SIMPLE _ => NONE | AtomSCC.RECURSIVE nodes => SOME nodes)
          components
      fun tyToData (tyName: Atom.atom) : string * int * Ast.Exp.datbind =
        let val (id, datbind) = AtomTable.lookup typenameToBind tyName
        in (Atom.toString tyName, id, datbind)
        end
      val followTys: Atom.atom list -> Atom.atom list =
        List.concat o List.map (AtomSet.toList o AtomTable.lookup followTable)
      fun appendFollowTys tys = tys @ followTys tys
      val components: (string * int * Ast.Exp.datbind) list list =
        List.map (removeDuplicateDatbinds o List.map tyToData o appendFollowTys)
          components
      val idToRenamedDec: Ast.Exp.dec IntHashTable.hash_table =
        IntHashTable.mkTable (20, LibBase.NotFound)
      fun handleComponents i build (component :: rest) =
            let
              open Utils BuildAst
              val trackCount = countTypesAndConstructors (List.map #3 component)
              val trackSubst = componentSubstMap trackCount component
              val componentName = mkToken ("Component" ^ Int.toString i)
              val merged = concatDatbinds
                (List.map
                   (fn (typename, _, datbind) =>
                      substDatbind trackSubst (qualifiedTypePart typename)
                        datbind) component)
              val topdec = Ast.StrDec (simpleStructStrDec componentName
                (Ast.Str.DecCore (simpleDatatypeDec merged)))
            in
              (* For every datbind, add dec of typbinds that unpack the substituted type *)
              List.app
                (fn (typename, id, {elems, ...}) =>
                   let
                     val qualifiedPart = qualifiedTypePart typename
                     val decs =
                       ArraySlice.foldl
                         (fn ({tyvars, tycon, ...}, acc) =>
                            let
                              val tycon' = mkToken
                                (qualifiedPart ^ Token.toString tycon)
                              val tycon' = #trackTypename trackSubst tycon'
                                           handle _ => tycon
                              val tycon' = mkToken
                                (Token.toString componentName ^ "."
                                 ^ Token.toString tycon')
                              val tyvars = syntaxSeqToList tyvars
                              val dec =
                                MutRecTy.genSingleTypebind
                                  (fn tybind =>
                                     Ast.Exp.DecType
                                       { typee = mkReservedToken Token.Type
                                       , typbind = tybind
                                       })
                                  ( tycon
                                  , tyvars
                                  , Ast.Ty.Con
                                      { args = listToSyntaxSeq
                                          (List.map Ast.Ty.Var tyvars)
                                      , id = MaybeLongToken.make tycon'
                                      }
                                  )
                            in
                              dec :: acc
                            end) [] elems
                     val dec =
                       List.foldl (fn (a, b) => combineDecs a b)
                         Ast.Exp.DecEmpty decs
                   in
                     IntHashTable.insert idToRenamedDec (id, dec)
                   end) component;
              handleComponents (i + 1) (topdec :: build) rest
            end
        | handleComponents _ build [] = build
      val prependDecs: Ast.topdec list = handleComponents 1 [] components
      val prependDecs: {topdec: Ast.topdec, semicolon: Token.token option} Seq.t =
        Seq.fromList
          (List.map (fn topdec => {topdec = topdec, semicolon = NONE})
             prependDecs)
      val c = ref 0
      val visitor =
        { state = ()
        , goDecType = fn (_, dec, _) => dec
        , goDecDatatype = fn ((), dec, _, _) =>
            let val datbindId = !c before c := !c + 1
            in IntHashTable.lookup idToRenamedDec datbindId handle _ => dec
            end
        , onStructure = fn _ => fn () => ()
        , onFunctor = fn _ => fn () => ()
        }
      (* Visit every datatype declaration in topdecs and substitute each datatype Dec with a Dec
         of the list of unpacked type aliases based on datatype id.
      *)
      val topdecs' =
        Seq.map
          (fn {topdec, semicolon} =>
             { topdec = AstVisitor.goTopDec visitor topdec
             , semicolon = semicolon
             }) topdecs
    in
      Ast.Ast (Seq.append (prependDecs, topdecs'))
    end
end
