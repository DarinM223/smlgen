structure Utils =
struct
  open BuildAst

  fun capitalize s =
    case String.explode s of
      c :: cs => String.implode (Char.toUpper c :: cs)
    | _ => s

  fun mkTyVar var =
    let val var = Token.toString (stripToken var)
    in mkToken (String.substring (var, 1, String.size var - 1) ^ "_")
    end

  fun syntaxSeqToList SyntaxSeq.Empty = []
    | syntaxSeqToList (SyntaxSeq.One e) = [e]
    | syntaxSeqToList (SyntaxSeq.Many {elems, ...}) =
        ArraySlice.foldr (op::) [] elems

  fun syntaxSeqMap _ SyntaxSeq.Empty = SyntaxSeq.Empty
    | syntaxSeqMap f (SyntaxSeq.One e) =
        SyntaxSeq.One (f e)
    | syntaxSeqMap f (SyntaxSeq.Many {left, elems, delims, right}) =
        SyntaxSeq.Many
          { left = left
          , elems = ArraySlice.full (Array.fromList (List.map f
              (ArraySlice.foldr (op::) [] elems)))
          , delims = delims
          , right = right
          }

  fun showTy ty =
    case ty of
      Ty.Var tok => Token.toString (stripToken tok)
    | Ty.Record {elems, ...} =>
        "{"
        ^
        String.concatWith ","
          (List.map
             (fn {lab, ty, ...} =>
                Token.toString (stripToken lab) ^ ":" ^ showTy ty)
             (ArraySlice.foldr (op::) [] elems)) ^ "}"
    | Ty.Tuple {elems, ...} =>
        "("
        ^
        String.concatWith "," (List.map showTy
          (ArraySlice.foldr (op::) [] elems)) ^ ")"
    | Ty.Con {args, id} =>
        "(" ^ String.concatWith "," (List.map showTy (syntaxSeqToList args))
        ^ ")" ^ Token.toString (stripToken (MaybeLongToken.getToken id))
    | Ty.Arrow {from, to, ...} => showTy from ^ "->" ^ showTy to
    | Ty.Parens {ty, ...} => "(" ^ showTy ty ^ ")"
end
