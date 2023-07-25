(* non-recursive withtype & non-recursive datatype *)
datatype t = T' of int * string | Nil
withtype t' = t * int

val () = print (showT' (T' (1, "hello"), 2) ^ "\n")

(* non-recursive withtype with recursive datatype *)
datatype t = T' of string * t | T'' of t * t | Nil
withtype t' = { t: t, other: string }

val () = print (showT' {t = T' ("hello", T'' (Nil, Nil)), other = "world"} ^ "\n")

(* recursive withtype with recursive datatype *)
datatype t = T' of string * t' | Nil
withtype t' = t list

val () = print (showT' [T' ("hello", [T' ("world", []), Nil]), T' ("foo", [Nil]), Nil] ^ "\n")

(* TODO: test with type variables *)
(* TODO: test with multiple types in withtype *)