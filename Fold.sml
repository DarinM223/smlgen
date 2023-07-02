structure Fold =
struct
  fun fold (a, f) g = g (a, f)
  fun post (w, g) s =
    w (fn (a, h) => s (a, g o h))
  fun step0 h (a, f) =
    fold (h a, f)
  fun step1 h (a, f) b =
    fold (h (b, a), f)
  fun step2 h (a, f) b c =
    fold (h (b, c, a), f)
end
fun $ (a, f) = f a
