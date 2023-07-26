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

  fun prependToken str t =
    let
      val (prefix, t) =
        (Substring.splitr (fn ch => ch <> #".") o Substring.full
         o Token.toString) t
      val prepended =
        case Substring.string t of
          "t" => str
        | t => str ^ capitalize t
    in
      mkToken (Substring.string prefix ^ prepended)
    end

  fun sameTokens (t1, t2) =
    List.length t1 = List.length t2
    andalso List.all Token.same (ListPair.zip (t1, t2))

  fun syntaxSeqToList SyntaxSeq.Empty = []
    | syntaxSeqToList (SyntaxSeq.One e) = [e]
    | syntaxSeqToList (SyntaxSeq.Many {elems, ...}) =
        ArraySlice.foldr (op::) [] elems

  fun listToSyntaxSeq [] = SyntaxSeq.Empty
    | listToSyntaxSeq [e] = SyntaxSeq.One e
    | listToSyntaxSeq (elems as (_ :: es)) =
        SyntaxSeq.Many
          { left = openParenTok
          , right = closeParenTok
          , elems = Seq.fromList elems
          , delims = Seq.fromList (List.map (fn _ => commaTok) es)
          }

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
        if ArraySlice.length elems = 1 then
          showTy (parensTy (ArraySlice.sub (elems, 0)))
        else
          "("
          ^
          String.concatWith "," (List.map showTy
            (ArraySlice.foldr (op::) [] elems)) ^ ")"
    | Ty.Con {args, id} =>
        "(" ^ String.concatWith "," (List.map showTy (syntaxSeqToList args))
        ^ ")" ^ Token.toString (stripToken (MaybeLongToken.getToken id))
    | Ty.Arrow {from, to, ...} => showTy from ^ "->" ^ showTy to
    | Ty.Parens {ty as Ty.Parens _, ...} => showTy ty
    | Ty.Parens {ty as Ty.Tuple _, ...} => showTy ty
    | Ty.Parens {ty as Ty.Record _, ...} => showTy ty
    | Ty.Parens {ty, ...} => "(" ^ showTy ty ^ ")"

  fun tySize ty =
    case ty of
      Ty.Var _ => 1
    | Ty.Record {elems, ...} =>
        ArraySlice.foldl (fn ({ty, ...}, acc) => acc + tySize ty) 1 elems
    | Ty.Tuple {elems, ...} =>
        ArraySlice.foldl (fn (ty, acc) => acc + tySize ty) 0 elems
    | Ty.Con {args, ...} =>
        List.foldl (fn (ty, acc) => acc + tySize ty) 1 (syntaxSeqToList args)
    | Ty.Arrow {from, to, ...} => tySize from + tySize to
    | Ty.Parens {ty, ...} => tySize ty

  fun stripParens (Pat.Parens {pat, ...}) = pat
    | stripParens (ty as Pat.Tuple {elems, ...}) =
        if ArraySlice.length elems = 1 then ArraySlice.sub (elems, 0) else ty
    | stripParens pat = pat

  fun destructTyPat fresh (Ty.Var _) =
        Pat.Const (fresh tTok)
    | destructTyPat fresh (Ty.Record {elems, ...}) =
        destructRecordPat'
          (List.map
             (fn {lab, ty, ...} => (lab, stripParens (destructTyPat fresh ty)))
             (ArraySlice.foldr (op::) [] elems))
    | destructTyPat fresh (Ty.Tuple {elems, ...}) =
        destructTuplePat (List.map (stripParens o destructTyPat fresh)
          (ArraySlice.foldr (op::) [] elems))
    | destructTyPat fresh (Ty.Con {id, args, ...}) =
        let
          val id = MaybeLongToken.getToken id
        in
          case (Token.toString id, syntaxSeqToList args) of
            ("ref", [ty]) => parensPat (conPat id (destructTyPat fresh ty))
          | ("unit", []) => wildPat
          | _ => Pat.Const (fresh tTok)
        end
    | destructTyPat _ (Ty.Arrow _) = wildPat
    | destructTyPat fresh (Ty.Parens {ty, ...}) = destructTyPat fresh ty
end
