fun $ (a, f) = f a
signature FOLD =
sig
  type ('a, 'b, 'c, 'd) step = 'a * ('b -> 'c) -> 'd
  type ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) step -> 'd
  type ('a1, 'a2, 'b, 'c, 'd) step0 = ('a1, 'b, 'c, ('a2, 'b, 'c, 'd) t) step
  type ('a11, 'a12, 'a2, 'b, 'c, 'd) step1 =
    ('a12, 'b, 'c, 'a11 -> ('a2, 'b, 'c, 'd) t) step
  type ('a11, 'a12, 'a13, 'a2, 'b, 'c, 'd) step2 =
    ('a13, 'b, 'c, 'a11 -> 'a12 -> ('a2, 'b, 'c, 'd) t) step
  val fold: 'a * ('b -> 'c) -> ('a, 'b, 'c, 'd) t
  val lift0: ('a1, 'a2, 'a2, 'a2, 'a2) step0 -> ('a1, 'a2, 'b, 'c, 'd) step0
  val post: ('a, 'b, 'c1, 'd) t * ('c1 -> 'c2) -> ('a, 'b, 'c2, 'd) t
  val step0: ('a1 -> 'a2) -> ('a1, 'a2, 'b, 'c, 'd) step0
  val step1: ('a11 * 'a12 -> 'a2) -> ('a11, 'a12, 'a2, 'b, 'c, 'd) step1
  val step2: ('a11 * 'a12 * 'a13 -> 'a2)
             -> ('a11, 'a12, 'a13, 'a2, 'b, 'c, 'd) step2
end
structure Fold :> FOLD =
struct
  type ('a, 'b, 'c, 'd) step = 'a * ('b -> 'c) -> 'd
  type ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) step -> 'd
  type ('a1, 'a2, 'b, 'c, 'd) step0 = ('a1, 'b, 'c, ('a2, 'b, 'c, 'd) t) step
  type ('a11, 'a12, 'a2, 'b, 'c, 'd) step1 =
    ('a12, 'b, 'c, 'a11 -> ('a2, 'b, 'c, 'd) t) step
  type ('a11, 'a12, 'a13, 'a2, 'b, 'c, 'd) step2 =
    ('a13, 'b, 'c, 'a11 -> 'a12 -> ('a2, 'b, 'c, 'd) t) step
  fun fold (a: 'a, f: 'b -> 'c) (g: ('a, 'b, 'c, 'd) step) : 'd = g (a, f)
  fun step0 (h: 'a1 -> 'a2) (a1: 'a1, f: 'b -> 'c) : ('a2, 'b, 'c, 'd) t =
    fold (h a1, f)
  fun step1 (h: 'a11 * 'a12 -> 'a2) (a12: 'a12, f: 'b -> 'c) (a11: 'a11) :
    ('a2, 'b, 'c, 'd) t =
    fold (h (a11, a12), f)
  fun step2 (h: 'a11 * 'a12 * 'a13 -> 'a2) (a13: 'a13, f: 'b -> 'c) (a11: 'a11)
    (a12: 'a12) : ('a2, 'b, 'c, 'd) t =
    fold (h (a11, a12, a13), f)
  fun lift0 (s: ('a1, 'a2, 'a2, 'a2, 'a2) step0) (a: 'a1, f: 'b -> 'c) :
    ('a2, 'b, 'c, 'd) t =
    fold (fold (a, fn a => a) s $, f)
  fun post (w: ('a, 'b, 'c1, 'd) t, g: 'c1 -> 'c2) (s: ('a, 'b, 'c2, 'd) step) :
    'd =
    w (fn (a, h) => s (a, g o h))
end
