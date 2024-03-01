signature GATHER_TYPES =
sig
  val run:
    Ast.ast
    -> (int * Ast.Exp.datbind) AtomTable.hash_table
       * Ast.Exp.typbind AtomTable.hash_table
end

signature RECURSIVE_MODULES =
sig
  type subst_table
  val emptySubstTable: unit -> subst_table
  val gen: Ast.ast -> Ast.ast * subst_table
  val substArgs: subst_table
                 -> (string list * Utils.gen) list
                 -> (string list * Utils.gen) list
end
