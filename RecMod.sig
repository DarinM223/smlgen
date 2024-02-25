signature GATHER_TYPES =
sig
  val run:
    Ast.ast
    -> (int * Ast.Exp.datbind) AtomTable.hash_table
       * Ast.Exp.typbind AtomTable.hash_table
end

signature RECURSIVE_MODULES =
sig
  val gen: Ast.ast -> Ast.ast
end
