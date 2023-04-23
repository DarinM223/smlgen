signature CONVERT_VALUE =
sig
  type t
  val unit: t
  val const: Token.token -> t
  val app: Token.token -> t -> t
  val parens: t -> t
end
functor ConvertFn(Value: CONVERT_VALUE) =
struct
  open BuildAst

  type constr =
    { arg: {off: Token.token, ty: Ast.Ty.ty} option
    , id: Token.token
    , opp: Token.token option
    }

  fun ins (is, constr: constr) =
    let
      val head =
        case constr of
          {arg = SOME _, ...} => Value.const quesTok
        | _ => Value.unit
      val head = Value.app (List.hd is) head
    in
      List.foldl (fn (i, acc) => Value.app i (Value.parens acc)) head
        (List.tl is)
    end
  fun constr ({arg = SOME _, id, ...}: constr) =
        Value.app id (Value.const quesTok)
    | constr {id, ...} = Value.app id Value.unit
end

structure GenericGen =
struct
  structure SCC =
    GraphSCCFn (struct type ord_key = int val compare = Int.compare end)
  structure ExpValue: CONVERT_VALUE =
  struct
    open BuildAst
    open Ast.Exp
    type t = exp
    val unit = unitExp
    val const = Const
    val app = fn tok => fn a => App {left = Const tok, right = a}
    val parens = parensExp
  end
  structure PatValue: CONVERT_VALUE =
  struct
    open BuildAst
    open Ast.Pat
    type t = pat
    val unit = unitPat
    val const = Const
    val app = fn tok =>
      fn a => Pat.Con {opp = NONE, id = MaybeLongToken.make tok, atpat = a}
    val parens = parensPat
  end
  structure ConvertExp = ConvertFn(ExpValue)
  structure ConvertPat = ConvertFn(PatValue)

  fun genTy (ty: Ast.Ty.ty) : Ast.Exp.exp =
    let open BuildAst
    in unitExp
    end

  fun genConstrs constrs =
    let
      open BuildAst
      val c0tok = mkToken "C0'"
      val c1tok = mkToken "C1'"
      val constrs' =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             App
               { left = App {left = Const c1tok, right = Const (stringTok id)}
               , right = genTy ty
               }
            | {id, ...} =>
             App {left = Const c0tok, right = Const (stringTok id)}) constrs
      val plusTok = mkToken "+`"
      val dataExp =
        List.foldl (fn (e, acc) => Infix {left = acc, id = plusTok, right = e})
          (List.hd constrs') (List.tl constrs')
      val inrTok = mkToken "INR"
      val inlTok = mkToken "INL"
      fun buildINs 0 [_] = [[inrTok]]
        | buildINs n [_] =
            [inlTok :: List.tabulate (n - 1, fn _ => inlTok)]
        | buildINs 0 (_ :: cs) =
            [inrTok] :: buildINs 1 cs
        | buildINs n (_ :: cs) =
            (inrTok :: List.tabulate (n, fn _ => inlTok)) :: buildINs (n + 1) cs
        | buildINs _ [] = []
      val revConstrs = List.rev constrs
      val ins = buildINs 0 revConstrs
      val toINs =
        List.map
          (fn (is, constr) =>
             (ConvertPat.constr constr, ConvertExp.ins (is, constr)))
          (ListPair.zip (ins, revConstrs))
      val fromINs =
        List.map
          (fn (is, constr) =>
             (ConvertPat.ins (is, constr), ConvertExp.constr constr))
          (ListPair.zip (ins, revConstrs))
    in
      App
        { left = App {left = Const (mkToken "data'"), right = parensExp dataExp}
        , right = tupleExp [multFnExp toINs, multFnExp fromINs]
        }
    end

  fun genDatabind ({elems, ...}: Ast.Exp.datbind) =
    let
      open BuildAst
      val elems = ArraySlice.foldr (op::) [] elems
      val tys =
        List.map
          (fn {tycon, elems, ...} => (tycon, ArraySlice.foldr (op::) [] elems))
          elems
      val c = ref 0
      exception Beta
      val tyTokToId: int AtomTable.hash_table = AtomTable.mkTable (100, Beta)
      val tyLinks: IntListSet.set IntHashTable.hash_table =
        IntHashTable.mkTable (100, Beta)
      val tyData: (Token.token * ConvertExp.constr list) IntHashTable.hash_table =
        IntHashTable.mkTable (100, Beta)
      fun addLink i j =
        let val data = IntHashTable.lookup tyLinks i
        in IntHashTable.insert tyLinks (i, IntListSet.add (data, j))
        end
      fun buildLinks _ (Ast.Ty.Var _) = ()
        | buildLinks i (Ast.Ty.Record {elems, ...}) =
            ArraySlice.app (buildLinks i o #ty) elems
        | buildLinks i (Ast.Ty.Tuple {elems, ...}) =
            ArraySlice.app (buildLinks i) elems
        | buildLinks i (Ast.Ty.Con {id, args, ...}) =
            let
              val tok = Atom.atom (Token.toString (MaybeLongToken.getToken id))
            in
              case AtomTable.find tyTokToId tok of
                SOME j => addLink i j
              | NONE => ();
              case args of
                Ast.SyntaxSeq.Empty => ()
              | Ast.SyntaxSeq.One ty => buildLinks i ty
              | Ast.SyntaxSeq.Many {elems, ...} =>
                  ArraySlice.app (buildLinks i) elems
            end
        | buildLinks i (Ast.Ty.Arrow {from, to, ...}) =
            (buildLinks i from; buildLinks i to)
        | buildLinks i (Ast.Ty.Parens {ty, ...}) = buildLinks i ty
      val roots =
        List.map
          (fn (ty, constrs) =>
             let
               val i = !c before c := !c + 1
               val () = AtomTable.insert tyTokToId
                 (Atom.atom (Token.toString ty), i)
               val () = IntHashTable.insert tyLinks (i, IntListSet.empty)
               val () = IntHashTable.insert tyData (i, (ty, constrs))
             in
               i
             end) tys
      val () =
        List.app
          (fn (i, (_, constrs)) =>
             List.app
               (fn {arg = SOME {ty, ...}, ...} => buildLinks i ty | _ => ())
               constrs) (ListPair.zip (roots, tys))
      val scc: SCC.component list = SCC.topOrder'
        { roots = roots
        , follow = IntListSet.toList o IntHashTable.lookup tyLinks
        }
      val genericTok = MaybeLongToken.make (mkToken "Generic")
      val openTok = mkReservedToken Open
      val openGeneric = singleLetExp (DecOpen
        {openn = openTok, elems = ArraySlice.full (Array.fromList [genericTok])})
      fun handleComponent (SCC.SIMPLE i) =
            let val (ty, _) = IntHashTable.lookup tyData i
            in valDec (identPat ty) (openGeneric unitExp)
            end
        | handleComponent (SCC.RECURSIVE is) =
            let
              val datas = List.map (IntHashTable.lookup tyData) is
              val tys = List.map #1 datas
              val exps = List.map (genConstrs o #2) datas
              val andTok = mkToken "&"
              val pat =
                List.foldl
                  (fn (ty, acc) =>
                     Pat.Infix {left = acc, id = andTok, right = identPat ty})
                  (identPat (List.hd tys)) (List.tl tys)
              val lam = singleFnExp pat
                (List.foldl
                   (fn (e, acc) => Infix {left = acc, id = andTok, right = e})
                   (List.hd exps) (List.tl exps))
              val ys =
                let
                  val y = mkToken "Y"
                  val ys = List.map (fn _ => Const y) tys
                in
                  (if List.length ys = 1 then fn e => e else parensExp)
                    (List.foldl
                       (fn (e, acc) =>
                          App
                            { left = Const (mkToken "Tie.*`")
                            , right = tupleExp [acc, e]
                            }) (Const y) (List.tl ys))
                end
              val app =
                List.foldl (fn (e, acc) => App {left = acc, right = e})
                  (Const (mkToken "Tie.fix")) [ys, parensExp lam]
            in
              valDec pat (openGeneric app)
            end
    in
      multDec (List.map handleComponent (List.rev scc))
    end

  val gen =
    {genTypebind = fn _ => raise Fail "generic", genDatabind = genDatabind}
end
