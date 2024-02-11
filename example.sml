structure Use =
struct
  (* Add t -> Use.t to substitution map *)
  datatype t =
    Use of {value: Value.t ref, user: Value.t, prev: t ref, next: t ref}
end

structure Value =
struct
  type id = int
  datatype value =
    Instr of Instruction.t
  | Lit of Literal.t
  | Argument of Argument.t

  datatype t = Value of {id: id, value: value ref, uses: Use.t option ref}
end

structure Literal = struct
end

structure Argument = struct
end

(* Add components at the end so that the merged datatypes can use the  *)
structure Component1 = struct

end

structure Value = struct
end

val () = print "Hello world\n"
