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

  val splitPrefixFromTypeString =
    (fn (p, t) => (Substring.string p, Substring.string t))
    o Substring.splitr (fn ch => ch <> #".") o Substring.full
  val splitPrefixFromType = splitPrefixFromTypeString o Token.toString
  fun prependTokenOrDefault def str t =
    let
      val (prefix, t) = splitPrefixFromType t
      val prepended = if t = "t" then def else str ^ capitalize t
    in
      mkToken (prefix ^ prepended)
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

  (* Converts a type into a normal form so it can be hashed.
     Parenthesis are eliminated and all tokens are stripped.
   *)
  fun normalize (Ty.Var tok) =
        Ty.Var (stripToken tok)
    | normalize (Ty.Record {left, elems, delims, right}) =
        Ty.Record
          { left = stripToken left
          , elems =
              Seq.map
                (fn {lab, colon, ty} =>
                   { lab = stripToken lab
                   , colon = stripToken colon
                   , ty = normalize ty
                   }) elems
          , delims = Seq.map stripToken delims
          , right = stripToken right
          }
    | normalize (Ty.Tuple {elems, delims}) =
        if ArraySlice.length elems = 1 then
          normalize (parensTy (ArraySlice.sub (elems, 0)))
        else
          Ty.Tuple
            { elems = Seq.map normalize elems
            , delims = Seq.map stripToken delims
            }
    | normalize (Ty.Con {args, id}) =
        Ty.Con
          { args = syntaxSeqMap normalize args
          , id = MaybeLongToken.make (stripToken (MaybeLongToken.getToken id))
          }
    | normalize (Ty.Arrow {from, to, arrow}) =
        Ty.Arrow
          {from = normalize from, to = normalize to, arrow = stripToken arrow}
    | normalize (Ty.Parens {ty, ...}) = normalize ty

  fun prettyTy ty =
    case ty of
      Ty.Var tok => Token.toString tok
    | Ty.Record {elems, ...} =>
        "{"
        ^
        String.concatWith ", "
          (List.map
             (fn {lab, ty, ...} => Token.toString lab ^ ": " ^ prettyTy ty)
             (Seq.toList elems)) ^ "}"
    | Ty.Tuple {elems, ...} =>
        "(" ^ String.concatWith " * " (List.map prettyTy (Seq.toList elems))
        ^ ")"
    | Ty.Con {args, id} =>
        let
          val conStr = Token.toString (MaybeLongToken.getToken id)
        in
          case syntaxSeqToList args of
            [] => conStr
          | [arg] => prettyTy arg ^ " " ^ conStr
          | args =>
              "(" ^ String.concatWith ", " (List.map prettyTy args) ^ ") "
              ^ conStr
        end
    | Ty.Arrow {from, to, ...} => prettyTy from ^ " -> " ^ prettyTy to
    | Ty.Parens {ty, ...} => "(" ^ prettyTy ty ^ ")"

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

  fun destructTyPat' _ fresh (Ty.Var _) =
        Pat.Const (fresh tTok)
    | destructTyPat' intoRefs fresh (Ty.Record {elems, ...}) =
        destructRecordPat'
          (List.map
             (fn {lab, ty, ...} =>
                (lab, stripParens (destructTyPat' intoRefs fresh ty)))
             (Seq.toList elems))
    | destructTyPat' intoRefs fresh (Ty.Tuple {elems, ...}) =
        destructTuplePat
          (List.map (stripParens o destructTyPat' intoRefs fresh)
             (Seq.toList elems))
    | destructTyPat' intoRefs fresh (Ty.Con {id, args, ...}) =
        let
          val id = MaybeLongToken.getToken id
        in
          case (Token.toString id, syntaxSeqToList args) of
            ("ref", [ty]) =>
              if intoRefs then
                parensPat (conPat id (destructTyPat' intoRefs fresh ty))
              else
                Pat.Const (fresh tTok)
          | ("unit", []) => wildPat
          | _ => Pat.Const (fresh tTok)
        end
    | destructTyPat' _ _ (Ty.Arrow _) = wildPat
    | destructTyPat' intoRefs fresh (Ty.Parens {ty, ...}) =
        destructTyPat' intoRefs fresh ty
  val destructTyPat = destructTyPat' true
  val destructTyPatNoRefs = destructTyPat' false

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

  val aliasTypes =
    [ ("List.list", "list")
    , ("Option.option", "option")
    , ("Int.int", "int")
    , ("Real.real", "real")
    , ("Math.real", "real")
    , ("Array.array", "array")
    , ("Array.vector", "vector")
    , ("Vector.vector", "vector")
    , ("String.string", "string")
    , ("String.char", "char")
    , ("CharVector.vector", "string")
    , ("CharVector.elem", "char")
    , ("WideCharVector.vector", "WideString.string")
    , ("WideCharVector.elem", "WideChar.char")
    , ("BoolVector.elem", "bool")
    , ("IntVector.elem", "int")
    , ("WordVector.elem", "word")
    , ("RealVector.elem", "real")
    , ("LargeIntVector.elem", "LargeInt.int")
    , ("LargeWordVector.elem", "LargeWord.word")
    , ("LargeRealVector.elem", "LargeReal.real")
    , ("WideString.char", "WideChar.char")
    , ("Substring.string", "string")
    , ("Substring.char", "char")
    , ("WideSubstring.string", "WideString.string")
    , ("WideSubstring.char", "WideChar.char")
    , ("Text.String.string", "string")
    , ("Text.Char.char", "char")
    , ("Text.CharVector.vector", "string")
    , ("Text.CharArray.array", "CharArray.array")
    , ("Text.CharVectorSlice.slice", "Substring.substring")
    , ("Text.CharArraySlice.slice", "CharArraySlice.slice")
    , ("WideText.String.string", "WideString.string")
    , ("WideText.Char.char", "WideChar.char")
    , ("WideText.CharVector.vector", "WideString.string")
    , ("WideText.CharArray.array", "WideCharArray.array")
    , ("WideText.CharVectorSlice.slice", "WideSubstring.substring")
    , ("WideText.CharArraySlice.slice", "WideCharArraySlice.slice")
    , ("Char.char", "char")
    , ("Char.string", "string")
    , ("WideChar.string", "WideString.string")
    , ("Word.word", "word")
    , ("Bool.bool", "bool")
    , ("General.order", "order")
    , ("General.unit", "unit")
    , ("CharVectorSlice.slice", "Substring.substring")
    , ("WideCharVectorSlice.slice", "WideSubstring.substring")
    , ("Text.Char.char", "char")
    , ("TextPrimIO.array", "CharArray.array")
    , ("TextPrimIO.vector", "string")
    , ("TextPrimIO.elem", "char")
    , ("WideTextPrimIO.array", "WideCharArray.array")
    , ("WideTextPrimIO.vector", "WideString.string")
    , ("WideTextPrimIO.elem", "WideChar.char")
    , ("BinPrimIO.array", "Word8Array.array")
    , ("BinPrimIO.vector", "Word8Vector.vector")
    , ("BinPrimIO.elem", "Word8.word")
    , ("BinPrimIO.pos", "Position.int")
    ]
  val aliasTypeMap =
    List.foldl
      (fn ((k, v), acc) => AtomRedBlackMap.insert' ((Atom.atom k, v), acc))
      AtomRedBlackMap.empty aliasTypes

  val rewriteAlias = fn atom => AtomRedBlackMap.find (aliasTypeMap, atom)
end
