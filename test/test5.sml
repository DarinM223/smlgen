datatype ('a, 'b) stmt =
  Assign of 'a * ('a, 'b) expr
| If of ('a, 'b) expr * ('b, 'a) stmt list * ('a, 'b) stmt list
and ('a, 'b) expr =
  Stmt of ('a, 'a) stmt
| Int of 'b
| Bop of ('b, 'a) expr * ('a, 'b) expr

datatype 'a foo = Foo of 'a * 'a foo * string foo | Nil