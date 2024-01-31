structure GatherTypes =
struct
  fun visitor typenameToBind =
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
          in (* TODO: rewrite datbind with withtypees *)
            ArraySlice.app
              (fn typ =>
                 AtomTable.insert typenameToBind (Atom.atom typ, datbind)) types;
            dec
          end
    , onStructure = fn strid => fn path => Token.toString strid :: path
    , onFunctor = fn funid => fn path => Token.toString funid :: path
    }

  fun run (Ast.Ast topdecs : Ast.t) =
    let
      val typenameToBind: Ast.Exp.datbind AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
    in
      Seq.map
        (fn {topdec, semicolon} =>
           { topdec = AstVisitor.goTopDec (visitor typenameToBind) topdec
           , semicolon = semicolon
           }) topdecs;
      typenameToBind
    end
end

structure RecMod: RECURSIVE_MODULES =
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
              val idAtom = Atom.atom
                (Token.toString (MaybeLongToken.getToken id))
            in
              if AtomTable.inDomain followTable idAtom then
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

  val qualifiedTypePart =
    Substring.string o #1 o (Substring.splitr (fn #"." => false | _ => true))
    o Substring.full
  val serialize = String.map (fn #"." => #"_" | ch => ch)

  fun componentSubstMap ({trackTypename, trackConstructor}: int track)
    (component: (string * Ast.Exp.datbind) list) =
    let
      val typenameRename: string AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
      val constrRename: string AtomTable.hash_table =
        AtomTable.mkTable (20, LibBase.NotFound)
    in
      List.app
        (fn (typename, {elems, ...}) =>
           ArraySlice.app
             (fn {tycon, elems, ...} =>
                ( if trackTypename tycon > 1 then
                    AtomTable.insert typenameRename
                      ( Atom.atom
                          (qualifiedTypePart typename ^ Token.toString tycon)
                      , serialize
                          (qualifiedTypePart typename ^ Token.toString tycon)
                      )
                  else
                    ()
                ; ArraySlice.app
                    (fn {id, ...} =>
                       if trackConstructor id > 1 then
                         AtomTable.insert constrRename
                           ( Atom.atom
                               (qualifiedTypePart typename ^ Token.toString id)
                           , serialize
                               (qualifiedTypePart typename
                                ^ Token.toString tycon ^ "." ^ Token.toString id)
                           )
                       else
                         ()) elems
                )) elems) component;
      (* TODO: debugging printing remove this after *)
      AtomTable.appi (fn (a, s) => print (Atom.toString a ^ " -> " ^ s ^ "\n"))
        typenameRename;
      AtomTable.appi (fn (a, s) => print (Atom.toString a ^ " -> " ^ s ^ "\n"))
        constrRename;
      { trackTypename =
          Utils.mkToken o AtomTable.lookup typenameRename o Atom.atom
          o Token.toString
      , trackConstructor =
          Utils.mkToken o AtomTable.lookup constrRename o Atom.atom
          o Token.toString
      }
    end

  (*
  1. Track structure levels in environment.
     First pass: For every datatype, make a map from full name (including structures) to the datatype.
     Second pass: Track the current environment of structure name to datatype as well as the current
     structure level. If there is a link to the global environment and the current environment it should
     prefer the current environment.
  2. For every datatype, add links to other datatypes and also store the datatype constructors and types.
  3. Calculate the SCCs of the datatypes to find the connected datatype components.
  4. For each component, generate a merged structure name at the beginning and merge the datatypes
     into a single mutually recursive datatype.
  5. Rewrite the original structures to unpack the corresponding type in the recursive datatype.

  TODO: handle type aliases
  *)
  fun gen ast =
    let
      val typenameToBind = GatherTypes.run ast
      val followTable: AtomSet.set AtomTable.hash_table =
        AtomTable.mkTable (AtomTable.numItems typenameToBind, LibBase.NotFound)
      val () =
        AtomTable.appi
          (fn (typename, _) =>
             AtomTable.insert followTable (typename, AtomSet.empty))
          typenameToBind
      val () =
        AtomTable.appi
          (fn (typename, datbind) => addLinks (followTable, typename, datbind))
          typenameToBind
      val roots = List.map #1 (AtomTable.listItemsi followTable)
      val components = AtomSCC.topOrder'
        {roots = roots, follow = AtomSet.toList o AtomTable.lookup followTable}
      val components: (string * Ast.Exp.datbind) list list =
        List.map
          (List.map (fn a =>
             (Atom.toString a, AtomTable.lookup typenameToBind a)))
          (List.mapPartial
             (fn AtomSCC.SIMPLE _ => NONE
               | AtomSCC.RECURSIVE nodes =>
                SOME (AtomSet.toList (AtomSet.fromList nodes))) components)
      fun printComponents i (component :: rest) =
            let
              val trackCount = countTypesAndConstructors (List.map #2 component)
              val trackSubst = componentSubstMap trackCount component
            in
              print ("Component " ^ Int.toString i ^ ":\n");
              List.app
                (fn (typename, datbind) =>
                   print
                     (typename ^ " "
                      ^
                      TerminalColorString.toString {colors = true}
                        (Utils.prettyDatbind datbind) ^ "\n")) component;
              print "Merged:\n";
              print
                (TerminalColorString.toString {colors = true}
                   (Utils.prettyDatbind (Utils.concatDatbinds
                      (List.map #2 component))));
              print "\n\n";
              printComponents (i + 1) rest
            end
        | printComponents _ [] = ()
    in
      print "Components: \n";
      printComponents 1 components;
      ast
    end
end
