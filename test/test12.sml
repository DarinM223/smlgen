infix & *` +`

datatype ('a, 'b) stmt =
  Assign of 'a * ('a, 'b, 'a) expr
| If of ('a, 'b, 'b) expr * ('b, 'a) stmt list * ('a, 'b) stmt list
and ('d, 'c, 'b) expr =
  Stmt of ('b, 'd) stmt
| Int of 'd * 'b
| Bop of ('d, 'b, 'c) expr * ('c, 'b, 'd) expr

val () = print (showStmt (Int.toString, fn a => a)
  (Assign (1, Bop (Int (1, "hello"), Int ("hello", 2)))) ^ "\n")

datatype ('a, 'b, 'c) stmt =
  Assign of 'b * ('a, 'c, 'b) expr
| If of ('c, 'b, 'a) expr * ('b, 'a, 'c) stmt list * ('b, 'a, 'c) stmt list
and ('c, 'd, 'b) expr =
  Stmt of ('b, 'd, 'c) stmt
| Int of 'd * 'b
| Bop of ('d, 'b, 'c) expr * ('c, 'b, 'd) expr

val () = print (showStmt (Int.toString, Real.toString, fn a => a)
  (Assign (2.0, Bop (Int (3.0, 2), Int (4.0, "hello")))) ^ "\n")

datatype ('a, 'b, 'c) stmt =
  Assign of 'b * expr
| If of expr * ('b, 'a, 'c) stmt list * ('b, 'a, 'c) stmt list
and expr =
  Stmt of (string, int, real) stmt
| Int of int
| Bop of expr * expr
