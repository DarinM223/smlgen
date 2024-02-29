structure Use =
struct
  datatype t =
    T of {value: Value.t ref, user: Value.t, prev: t ref, next: t ref}
end

structure Value =
struct
  type id = int

  datatype value =
    Instr of Instruction.t
  | Lit of Literal.t
  | Argument of Argument.t

  datatype t = T of {id: id, value: value ref, uses: Use.t option ref}
end

structure Literal =
struct
  datatype t =
    Bool of bool
  | Byte of int
  | Int of int
  | Long of int
  | Double of real
  | Global of Global.t
  | NullPointer of Type.t
  | Function of Function.t
  | ArrayString of string
  | ArrayVtable of int * Use.t list
  | AggregateClosure of Type.t * Use.t
end

structure Argument =
struct datatype t = T of {func: Function.t, type_: Type.t, decl_loc: Loc.t} end

structure Instruction =
struct
  structure Phi = struct type t = {args: Use.t list ref} end

  structure GetPointer =
  struct
    datatype 'a offset = PointerIndex of 'a | FieldIndex of int
    type value_offset = Value.t offset
    type use_offset = Use.t offset
    datatype t =
      T of
        {pointer: Use.t, pointer_offset: Use.t option, offsets: use_offset list}
  end
  structure Call =
  struct
    datatype t =
      T of {func: func, args: Use.t list, has_return: bool}
    and func =
      Value of Use.t
    | MirBuiltin of Builtin.t
  end

  datatype comparison = Eq | Neq | Lt | LtEq | Gt | GtEq

  datatype unary_operation = Neg | Not

  datatype binary_operation =
    Add
  | Sub
  | Mul
  | Div
  | Rem
  | And
  | Or
  | Xor
  | Shl
  | Shr
  | Shrl

  datatype instr =
    Phi of Phi.t
  | Call of Call.t
  | StackAlloc of Type.t
  | Load of Use.t
  | Store of Use.t * Use.t
  | GetPointer of GetPointer.t
  | Unary of unary_operation * Use.t
  | Binary of binary_operation * Use.t * Use.t
  | Cmp of comparison * Use.t * Use.t
  | Cast of Use.t
  | Trunc of Use.t
  | SExt of Use.t
  | ZExt of Use.t
  | IntToFloat of Use.t
  | FloatToInt of Use.t
  | Ret of Use.t option
  | Continue of Block.t
  | Branch of {test: Use.t, continue: Block.t, jump: Block.t}
  | Unreachable
  | Mov of Use.t

  and t =
    T of
      { type_: Type.t ref
      , instr: instr ref
      , block: Block.t ref
      , prev: Value.t ref
      , next: Value.t ref
      }
end

structure Program =
struct
  datatype t =
    T of
      { globals: Global.t AtomMap.t ref
      , funcs: Function.t AtomMap.t ref
      , types: Aggregate.t AtomMap.t ref
      , main_func: Function.t ref
      }
end

structure Block =
struct
  type id = int
  datatype t =
    T of
      { id: id
      , func: Function.t
      , instructions: instructions option ref
      , prev_blocks: Block.t list ref
      }
  and instructions =
    Instructions of {first: Value.t ref, last: Value.t ref}
end

structure Global =
struct
  datatype t =
    T of
      { name: label
      , loc: Loc.t
      , type_: Type.t
      , init_val: Use.t option ref
      , is_constant: bool
      , value: Value.t ref
      }
end

structure Function =
struct
  datatype t =
    T of
      { name: label
      , loc: Loc.t ref
      , params: Value.t list ref
      , return_type: Type.t option ref
      , start_block: Block.t ref
      , blocks: Block.t list ref
      , value: Value.t ref
      }
end
