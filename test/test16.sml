infix & *` +`

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

(* test with type variables *)

datatype 'a t = T' of 'a t' | Nil
withtype 'b t' = 'b * 'b t list

val () = print (showT' Int.toString (1, [Nil, T' (2, [Nil])]) ^ "\n")

datatype ('a, 'b) t = T' of 'a t' * 'b t' | Nil
withtype 'b t' = 'b * ('b, 'b) t

val () = print (show (Int.toString, fn a => a) (T' ((1, T' ((2, Nil), (3, Nil))), ("a", T' (("b", Nil), ("c", Nil)))))  ^ "\n")

(* test with multiple types in withtype *)

datatype ('a, 'b) t = T' of 'a t' * 'b t'' | Nil
withtype 'a t' = 'a * ('a, int) t
and 'a t'' = (string, 'a) t * 'a

val () = print (show (fn a => a, Int.toString) (T' (("a", T' (("b", Nil), (Nil, 1))), (T' (("c", Nil), (Nil, 3)), 2))) ^ "\n")