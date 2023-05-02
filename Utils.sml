structure Utils =
struct
  fun capitalize s =
    case String.explode s of
      c :: cs => String.implode (Char.toUpper c :: cs)
    | _ => s

  fun eqToken t1 t2 = Token.toString t1 = Token.toString t2
end
