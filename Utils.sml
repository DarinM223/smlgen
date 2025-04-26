structure Utils :> UTILS =
struct
  open Ast BuildAst TokenUtils Tokens

  fun capitalize s =
    case String.explode s of
      c :: cs => String.implode (Char.toUpper c :: cs)
    | _ => s

  fun mkTyVar var =
    let val var = Token.toString (stripToken var)
    in mkToken (String.substring (var, 1, String.size var - 1) ^ "_")
    end

  fun header vars =
    case List.map (Pat.Const o mkTyVar) vars of
      [] => (fn e => e)
    | vars => singleFnExp (destructTuplePat vars)

  fun prependTokenOrDefault def str t =
    let
      val (prefix, t) =
        (Substring.splitr (fn ch => ch <> #".") o Substring.full
         o Token.toString) t
      val prepended =
        case Substring.string t of
          "t" => def
        | t => str ^ capitalize t
    in
      mkToken (Substring.string prefix ^ prepended)
    end
  fun prependToken str t =
    prependTokenOrDefault str str t

  fun sameTokens (t1, t2) =
    List.length t1 = List.length t2
    andalso List.all Token.same (ListPair.zip (t1, t2))

  fun syntaxSeqToList SyntaxSeq.Empty = []
    | syntaxSeqToList (SyntaxSeq.One e) = [e]
    | syntaxSeqToList (SyntaxSeq.Many {elems, ...}) = Seq.toList elems

  val syntaxSeqLen = fn seq => List.length (syntaxSeqToList seq)

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
          {left = left, elems = Seq.map f elems, delims = delims, right = right}

  fun syntaxSeqMapTy _ SyntaxSeq.Empty = SyntaxSeq.Empty
    | syntaxSeqMapTy f (SyntaxSeq.One ty) =
        (case f ty of
           ty as Ty.Tuple _ => SyntaxSeq.One (parensTy ty)
         | ty as Ty.Arrow _ => SyntaxSeq.One (parensTy ty)
         | ty => SyntaxSeq.One ty)
    | syntaxSeqMapTy f (SyntaxSeq.Many {left, elems, delims, right}) =
        SyntaxSeq.Many
          {left = left, elems = Seq.map f elems, delims = delims, right = right}

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
             (Seq.toList elems)) ^ "}"
    | Ty.Tuple {elems, ...} =>
        if ArraySlice.length elems = 1 then
          showTy (parensTy (ArraySlice.sub (elems, 0)))
        else
          "(" ^ String.concatWith "," (List.map showTy (Seq.toList elems)) ^ ")"
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
             (Seq.toList elems))
    | destructTyPat fresh (Ty.Tuple {elems, ...}) =
        destructTuplePat
          (List.map (stripParens o destructTyPat fresh) (Seq.toList elems))
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

  fun combineDecs (Ast.Exp.DecMultiple {elems = elems1, delims = delims1})
        (Ast.Exp.DecMultiple {elems = elems2, delims = delims2}) =
        Ast.Exp.DecMultiple
          { elems = Seq.append (elems1, elems2)
          , delims = Seq.append (delims1, delims2)
          }
    | combineDecs (Ast.Exp.DecMultiple {elems, delims}) dec =
        Ast.Exp.DecMultiple
          { elems = Seq.append (elems, Seq.singleton dec)
          , delims = Seq.append (delims, Seq.singleton NONE)
          }
    | combineDecs dec (Ast.Exp.DecMultiple {elems, delims}) =
        Ast.Exp.DecMultiple
          { elems = Seq.fromList (dec :: Seq.toList elems)
          , delims = Seq.fromList (NONE :: Seq.toList delims)
          }
    | combineDecs dec1 dec2 =
        Ast.Exp.DecMultiple
          { elems = Seq.fromList [dec1, dec2]
          , delims = Seq.fromList [NONE, NONE]
          }

  val pretty = PrettierPrintAst.pretty
    {ribbonFrac = 1.0, maxWidth = 80, tabWidth = 4, indent = 2, debug = false}
  val prettyDec =
    pretty
    o (fn topdec => Ast.Ast (Seq.singleton {topdec = topdec, semicolon = NONE}))
    o Ast.StrDec o Ast.Str.DecCore
  fun prettyDatbind datbind =
    prettyDec
      (Ast.Exp.DecDatatype
         {datatypee = datatypeTok, datbind = datbind, withtypee = NONE})

  fun concatDatbinds (datbinds: Ast.Exp.datbind list) =
    let
      val datbinds = List.concat
        (List.map (fn datbind => Seq.toList (#elems datbind)) datbinds)
    in
      { delims = Seq.tabulate (fn _ => andKeyTok) (Int.max
          (0, List.length datbinds - 1))
      , elems = Seq.fromList datbinds
      }
    end

  val datbindTys = fn datbind =>
    let
      val result: Ast.Ty.ty list ref = ref []
      val visitor: AstVisitor.datbind_visitor =
        { mapTy = fn ty => (result := ty :: !result; ty)
        , mapTycon = fn t => t
        , mapConbind = fn t => t
        }
    in
      ignore (AstVisitor.goDatbind visitor datbind);
      List.rev (!result)
    end

  fun mapBase f file =
    let val {base, ext} = OS.Path.splitBaseExt file
    in OS.Path.joinBaseExt {base = f base, ext = ext}
    end
  fun mapBasename f fp =
    let
      val basename = FilePath.toUnixPath (FilePath.basename fp)
      val dirname = FilePath.dirname fp
      val basename = FilePath.fromUnixPath (f basename)
    in
      FilePath.join (dirname, basename)
    end
  val qualifiedTypePart =
    Substring.string o #1 o (Substring.splitr (fn #"." => false | _ => true))
    o Substring.full
  val typenameTypePart =
    Substring.string o #2 o (Substring.splitr (fn #"." => false | _ => true))
    o Substring.full

  type gen =
    { genTypebind: Ast.Exp.typbind -> Ast.Exp.dec
    , genDatabind: Ast.Exp.datbind -> Ast.Exp.typbind option -> Ast.Exp.dec
    }

  val emptyGen =
    { genTypebind = fn _ => Ast.Exp.DecEmpty
    , genDatabind = fn _ => fn _ => Ast.Exp.DecEmpty
    }
  fun addGen (gen1: gen) (gen2: gen) =
    { genTypebind = fn bind =>
        combineDecs (#genTypebind gen1 bind) (#genTypebind gen2 bind)
    , genDatabind = fn databind =>
        fn typebind =>
          combineDecs (#genDatabind gen1 databind typebind)
            (#genDatabind gen2 databind typebind)
    }
end
