datatype 'a t = T' of 'a * 'a list t

datatype 'a t = T' of ('a * 'a) t

datatype 'a t = T' of ('a * 'a * 'a * 'a * 'a) list t

datatype ('a, 'b) t = T' of (('a * 'a) list, 'b * 'b) t

(* This should work *)
datatype 'a t = T' of 'a t