infix &

datatype ('a, 'b) stmt =
  Assign of 'a * ('a, 'b) expr
| If of ('a, 'b) expr * ('b, 'a) stmt list * ('a, 'b) stmt list
and ('b, 'a) expr =
  Stmt of ('a, 'a) stmt
| Int of 'b
| Bop of ('b, 'a) expr * ('a, 'b) expr

datatype ('a, 'b) stmt =
  Assign of 'a * ('a, 'b) expr * ('a, int) expr * (string, 'b) expr
| If of ('a, 'b) expr * ('b, 'a) stmt list * ('a, 'b) stmt list
and ('c, 'd) expr =
  Stmt of ('c, 'c) stmt
| Int of 'd
| Bop of ('d, 'c) expr * ('c, 'd) expr

datatype ('a, 'b) stmt =
  Assign of 'a * 'a expr
| If of 'b expr * ('b, 'a) stmt list * ('a, 'b) stmt list
and 'a expr =
  Stmt of ('a, int) stmt * (string, 'a) stmt
| Int of 'a
| Bop of 'a expr * 'a expr

datatype 'a t = T of 'a t * int t * string t