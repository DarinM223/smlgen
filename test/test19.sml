structure Use =
struct
  datatype t =
    Use of {value: Value.t ref, user: Value.t, prev: t ref, next: t ref}
end

structure Value =
struct
  type id = int
  datatype value = Instr of id
  datatype t = Value of {id: id, value: value ref, uses: Use.t option ref}
end

structure Literal = struct end

structure Argument = struct end

structure Value = struct end
