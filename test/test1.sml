infix &

type 'a person = {name: string, age: int, data: 'a}

structure Bop =
struct
  datatype t = Add | Sub | Mul | Div
end

structure Anf =
struct
  type var = string
  val var = Generic.string
  datatype value = Int of int | Var of var | Glob of var

  datatype t =
    Halt of value
  | Fun of var * var list * t * t
  | Join of var * var option * t * t
  | Jump of var * value option
  | App of var * var * value list * t
  | Bop of var * Bop.t * value * value * t
  | If of value * t * t
  | Tuple of var * value list * t
  | Proj of var * var * int * t
end

datatype stmt =
  Assign of string * expr
| If of expr * stmt list * stmt list
and expr =
  Stmt of stmt
| Int of int
| Bop of expr * expr