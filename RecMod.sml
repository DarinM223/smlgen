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
      val datbinds =
        AtomTable.fold (fn (datbind, acc) => datbind :: acc) [] typenameToBind
    in
      AtomTable.appi
        (fn (typ, datbind) =>
           ( print (Atom.toString typ ^ ":\n")
           ; print
               (TerminalColorString.toString {colors = true}
                  (Utils.prettyDatbind datbind) ^ "\n\n")
           )) typenameToBind;
      print "Merged: \n";
      print
        (TerminalColorString.toString {colors = true}
           (Utils.prettyDatbind (Utils.concatDatbinds datbinds)) ^ "\n\n");
      ast
    end
end
