datatype files_data =
  FilesData of {depends: files_data list, data: string, fileName: string}

structure FoldFile =
struct
  val data =
    "fun $ (a, f) = f a\n\
    \signature FOLD =\n\
    \   sig\n\
    \      type ('a, 'b, 'c, 'd) step = 'a * ('b -> 'c) -> 'd\n\
    \      type ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) step -> 'd\n\
    \      type ('a1, 'a2, 'b, 'c, 'd) step0 =\n\
    \         ('a1, 'b, 'c, ('a2, 'b, 'c, 'd) t) step\n\
    \      type ('a11, 'a12, 'a2, 'b, 'c, 'd) step1 =\n\
    \         ('a12, 'b, 'c, 'a11 -> ('a2, 'b, 'c, 'd) t) step\n\
    \      type ('a11, 'a12, 'a13, 'a2, 'b, 'c, 'd) step2 =\n\
    \         ('a13, 'b, 'c, 'a11 -> 'a12 -> ('a2, 'b, 'c, 'd) t) step\n\
    \      val fold: 'a * ('b -> 'c) -> ('a, 'b, 'c, 'd) t\n\
    \      val lift0: ('a1, 'a2, 'a2, 'a2, 'a2) step0\n\
    \                 -> ('a1, 'a2, 'b, 'c, 'd) step0\n\
    \      val post: ('a, 'b, 'c1, 'd) t * ('c1 -> 'c2)\n\
    \                -> ('a, 'b, 'c2, 'd) t\n\
    \      val step0: ('a1 -> 'a2) -> ('a1, 'a2, 'b, 'c, 'd) step0\n\
    \      val step1: ('a11 * 'a12 -> 'a2)\n\
    \                 -> ('a11, 'a12, 'a2, 'b, 'c, 'd) step1\n\
    \      val step2: ('a11 * 'a12 * 'a13 -> 'a2)\n\
    \                 -> ('a11, 'a12, 'a13, 'a2, 'b, 'c, 'd) step2\n\
    \   end\n\
    \structure Fold:> FOLD =\n\
    \   struct\n\
    \      type ('a, 'b, 'c, 'd) step = 'a * ('b -> 'c) -> 'd\n\
    \      type ('a, 'b, 'c, 'd) t = ('a, 'b, 'c, 'd) step -> 'd\n\
    \      type ('a1, 'a2, 'b, 'c, 'd) step0 =\n\
    \         ('a1, 'b, 'c, ('a2, 'b, 'c, 'd) t) step\n\
    \      type ('a11, 'a12, 'a2, 'b, 'c, 'd) step1 =\n\
    \         ('a12, 'b, 'c, 'a11 -> ('a2, 'b, 'c, 'd) t) step\n\
    \      type ('a11, 'a12, 'a13, 'a2, 'b, 'c, 'd) step2 =\n\
    \         ('a13, 'b, 'c, 'a11 -> 'a12 -> ('a2, 'b, 'c, 'd) t) step\n\
    \      fun fold (a: 'a, f: 'b -> 'c)\n\
    \               (g: ('a, 'b, 'c, 'd) step): 'd =\n\
    \         g (a, f)\n\
    \      fun step0 (h: 'a1 -> 'a2)\n\
    \                (a1: 'a1, f: 'b -> 'c): ('a2, 'b, 'c, 'd) t =\n\
    \         fold (h a1, f)\n\
    \      fun step1 (h: 'a11 * 'a12 -> 'a2)\n\
    \                (a12: 'a12, f: 'b -> 'c)\n\
    \                (a11: 'a11): ('a2, 'b, 'c, 'd) t =\n\
    \         fold (h (a11, a12), f)\n\
    \      fun step2 (h: 'a11 * 'a12 * 'a13 -> 'a2)\n\
    \                (a13: 'a13, f: 'b -> 'c)\n\
    \                (a11: 'a11)\n\
    \                (a12: 'a12) : ('a2, 'b, 'c, 'd) t =\n\
    \         fold (h (a11, a12, a13), f)\n\
    \      fun lift0 (s: ('a1, 'a2, 'a2, 'a2, 'a2) step0)\n\
    \                (a: 'a1, f: 'b -> 'c): ('a2, 'b, 'c, 'd) t =\n\
    \         fold (fold (a, fn a => a) s $, f)\n\
    \      fun post (w: ('a, 'b, 'c1, 'd) t,\n\
    \                g: 'c1 -> 'c2)\n\
    \               (s: ('a, 'b, 'c2, 'd) step): 'd =\n\
    \         w (fn (a, h) => s (a, g o h))\n\
    \  end\n"

  val t = FilesData {depends = [], data = data, fileName = "Fold.sml"}
end

structure FruFile =
struct
  val data =
    "structure FunctionalRecordUpdate =\n\
    \ struct\n\
    \ local\n\
    \   fun next g (f, z) x =\n\
    \     g (f x, z)\n\
    \   fun f1 (f, z) x =\n\
    \     f (z x)\n\
    \   fun f2 z = next f1 z\n\
    \   fun f3 z = next f2 z\n\
    \   fun f4 z = next f3 z\n\
    \   fun f5 z = next f4 z\n\
    \   fun f6 z = next f5 z\n\
    \   fun f7 z = next f6 z\n\
    \   fun f8 z = next f7 z\n\
    \   fun f9 z = next f8 z\n\
    \   fun f10 z = next f9 z\n\
    \   fun f11 z = next f10 z\n\
    \   fun f12 z = next f11 z\n\
    \   fun f13 z = next f12 z\n\
    \   fun f14 z = next f13 z\n\
    \   fun f15 z = next f14 z\n\
    \   fun f16 z = next f15 z\n\
    \   fun f17 z = next f16 z\n\
    \   fun f18 z = next f17 z\n\
    \   fun f19 z = next f18 z\n\
    \   fun f20 z = next f19 z\n\
    \   fun f21 z = next f20 z\n\
    \   fun f22 z = next f21 z\n\
    \   fun f23 z = next f22 z\n\
    \   fun f24 z = next f23 z\n\
    \   fun f25 z = next f24 z\n\
    \   fun f26 z = next f25 z\n\
    \   fun f27 z = next f26 z\n\
    \   fun f28 z = next f27 z\n\
    \   fun f29 z = next f28 z\n\
    \   fun f30 z = next f29 z\n\
    \   fun c0 from = from\n\
    \   fun c1 from = c0 from f1\n\
    \   fun c2 from = c1 from f2\n\
    \   fun c3 from = c2 from f3\n\
    \   fun c4 from = c3 from f4\n\
    \   fun c5 from = c4 from f5\n\
    \   fun c6 from = c5 from f6\n\
    \   fun c7 from = c6 from f7\n\
    \   fun c8 from = c7 from f8\n\
    \   fun c9 from = c8 from f9\n\
    \   fun c10 from = c9 from f10\n\
    \   fun c11 from = c10 from f11\n\
    \   fun c12 from = c11 from f12\n\
    \   fun c13 from = c12 from f13\n\
    \   fun c14 from = c13 from f14\n\
    \   fun c15 from = c14 from f15\n\
    \   fun c16 from = c15 from f16\n\
    \   fun c17 from = c16 from f17\n\
    \   fun c18 from = c17 from f18\n\
    \   fun c19 from = c18 from f19\n\
    \   fun c20 from = c19 from f20\n\
    \   fun c21 from = c20 from f21\n\
    \   fun c22 from = c21 from f22\n\
    \   fun c23 from = c22 from f23\n\
    \   fun c24 from = c23 from f24\n\
    \   fun c25 from = c24 from f25\n\
    \   fun c26 from = c25 from f26\n\
    \   fun c27 from = c26 from f27\n\
    \   fun c28 from = c27 from f28\n\
    \   fun c29 from = c28 from f29\n\
    \   fun c30 from = c29 from f30\n\
    \   fun makeUpdate cX (from, from', to) record =\n\
    \     let\n\
    \       fun ops () = cX from'\n\
    \       fun vars f = to f record\n\
    \     in\n\
    \       Fold.fold ((vars, ops), fn (vars, _) => vars from)\n\
    \     end\n\
    \ in\n\
    \   fun makeUpdate0 z = makeUpdate c0 z\n\
    \   fun makeUpdate1 z = makeUpdate c1 z\n\
    \   fun makeUpdate2 z = makeUpdate c2 z\n\
    \   fun makeUpdate3 z = makeUpdate c3 z\n\
    \   fun makeUpdate4 z = makeUpdate c4 z\n\
    \   fun makeUpdate5 z = makeUpdate c5 z\n\
    \   fun makeUpdate6 z = makeUpdate c6 z\n\
    \   fun makeUpdate7 z = makeUpdate c7 z\n\
    \   fun makeUpdate8 z = makeUpdate c8 z\n\
    \   fun makeUpdate9 z = makeUpdate c9 z\n\
    \   fun makeUpdate10 z = makeUpdate c10 z\n\
    \   fun makeUpdate11 z = makeUpdate c11 z\n\
    \   fun makeUpdate12 z = makeUpdate c12 z\n\
    \   fun makeUpdate13 z = makeUpdate c13 z\n\
    \   fun makeUpdate14 z = makeUpdate c14 z\n\
    \   fun makeUpdate15 z = makeUpdate c15 z\n\
    \   fun makeUpdate16 z = makeUpdate c16 z\n\
    \   fun makeUpdate17 z = makeUpdate c17 z\n\
    \   fun makeUpdate18 z = makeUpdate c18 z\n\
    \   fun makeUpdate19 z = makeUpdate c19 z\n\
    \   fun makeUpdate20 z = makeUpdate c20 z\n\
    \   fun makeUpdate21 z = makeUpdate c21 z\n\
    \   fun makeUpdate22 z = makeUpdate c22 z\n\
    \   fun makeUpdate23 z = makeUpdate c23 z\n\
    \   fun makeUpdate24 z = makeUpdate c24 z\n\
    \   fun makeUpdate25 z = makeUpdate c25 z\n\
    \   fun makeUpdate26 z = makeUpdate c26 z\n\
    \   fun makeUpdate27 z = makeUpdate c27 z\n\
    \   fun makeUpdate28 z = makeUpdate c28 z\n\
    \   fun makeUpdate29 z = makeUpdate c29 z\n\
    \   fun makeUpdate30 z = makeUpdate c30 z\n\
    \   fun upd z =\n\
    \     Fold.step2\n\
    \       (fn (s, f, (vars, ops)) => (fn out => vars (s (ops ()) (out, f)), ops))\n\
    \       z\n\
    \   fun set z =\n\
    \     Fold.step2\n\
    \       (fn (s, v, (vars, ops)) =>\n\
    \          (fn out => vars (s (ops ()) (out, fn _ => v)), ops)) z\n\
    \ end\n\
    \end"

  val t =
    FilesData
      { depends = [FoldFile.t]
      , data = data
      , fileName = "FunctionalRecordUpdate.sml"
      }
end

structure LiteralFile =
struct
  val data =
    "structure Literal:>\n\
    \ sig\n\
    \    type 'a z\n\
    \    val A: ('a z, 'a z, 'a array, 'd) Fold.t\n\
    \    val V: ('a z, 'a z, 'a vector, 'd) Fold.t\n\
    \    val ` : ('a, 'a z, 'a z, 'b, 'c, 'd) Fold.step1\n\
    \ end =\n\
    \ struct\n\
    \    type 'a z = int * 'a option * ('a array -> unit)\n\
    \    val A =\n\
    \       fn z =>\n\
    \       Fold.fold\n\
    \       ((0, NONE, ignore),\n\
    \        fn (n, opt, fill) =>\n\
    \        case opt of\n\
    \           NONE =>\n\
    \              Array.tabulate (0, fn _ => raise Fail \"array0\")\n\
    \         | SOME x =>\n\
    \              let\n\
    \                 val a = Array.array (n, x)\n\
    \                 val () = fill a\n\
    \              in\n\
    \                 a\n\
    \              end)\n\
    \       z\n\
    \    val V = fn z => Fold.post (A, Array.vector) z\n\
    \    val ` =\n\
    \       fn z =>\n\
    \       Fold.step1\n\
    \       (fn (x, (i, _, fill)) =>\n\
    \        (i + 1,\n\
    \         SOME x,\n\
    \         fn a => (Array.update (a, i, x); fill a)))\n\
    \       z\n\
    \ end\n"

  val t =
    FilesData
      {depends = [FoldFile.t], data = data, fileName = "ArrayLiteral.sml"}
end

structure NumFile =
struct
  val data =
    "structure Num =\n\
    \  struct\n\
    \     fun make (op *, op +, i2x) iBase =\n\
    \         let\n\
    \            val xBase = i2x iBase\n\
    \            fun fst (x, _) = x\n\
    \         in\n\
    \            Fold.fold\n\
    \               ((i2x 0,\n\
    \                 fn (i, x) =>\n\
    \                    if 0 <= i andalso i < iBase then\n\
    \                       x * xBase + i2x i\n\
    \                    else\n\
    \                       raise Fail (concat\n\
    \                                      [\"Num: \", Int.toString i,\n\
    \                                       \" is not a valid digit in base \",\n\
    \                                       Int.toString iBase])),\n\
    \                fst)\n\
    \         end\n\
    \     fun I  ? = make (op *, op +, fn a => a) ?\n\
    \     fun II ? = make (op *, op +, IntInf.fromInt) ?\n\
    \     fun W  ? = make (op *, op +, Word.fromInt) ?\n\
    \     fun ` ? = Fold.step1 (fn (i, (x, step)) =>\n\
    \                              (step (i, x), step)) ?\n\
    \     val a = 10\n\
    \     val b = 11\n\
    \     val c = 12\n\
    \     val d = 13\n\
    \     val e = 14\n\
    \     val f = 15\n\
    \  end\n"

  val t =
    FilesData
      {depends = [FoldFile.t], data = data, fileName = "NumberLiteral.sml"}
end

structure Fold01NFile =
struct
  val data =
    "structure Fold01N =\n\
    \   struct\n\
    \      type ('input, 'accum1, 'accum2, 'answer, 'zero,\n\
    \            'a, 'b, 'c, 'd, 'e) t =\n\
    \         (('zero -> 'zero)\n\
    \          * ('accum2 -> 'answer)\n\
    \          * (unit -> 'zero)\n\
    \          * ('input -> 'accum1),\n\
    \          ('a -> 'b) * 'c * (unit -> 'a) * 'd,\n\
    \          'b,\n\
    \          'e) Fold.t\n\
    \       type ('input1, 'accum1, 'input2, 'accum2,\n\
    \            'a, 'b, 'c, 'd, 'e, 'f) step0 =\n\
    \         ('a * 'b * 'c * ('input1 -> 'accum1),\n\
    \          'b * 'b * (unit -> 'accum1) * ('input2 -> 'accum2),\n\
    \          'd, 'e, 'f) Fold.step0\n\
    \      type ('accum1, 'input, 'accum2,\n\
    \            'a, 'b, 'c, 'd, 'e, 'f, 'g) step1 =\n\
    \         ('a,\n\
    \          'b * 'c * 'd * ('a -> 'accum1),\n\
    \          'c * 'c * (unit -> 'accum1) * ('input -> 'accum2),\n\
    \          'e, 'f, 'g) Fold.step1\n\
    \   end\n\
    \signature FOLD_01N =\n\
    \   sig\n\
    \      type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) t =\n\
    \         ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) Fold01N.t\n\
    \      type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) step0 =\n\
    \         ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) Fold01N.step0\n\
    \      type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) step1 =\n\
    \         ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) Fold01N.step1\n\
    \      val fold:\n\
    \         {finish: 'accum2 -> 'answer,\n\
    \          start: 'input -> 'accum1,\n\
    \          zero: 'zero}\n\
    \         -> ('input, 'accum1, 'accum2, 'answer, 'zero,\n\
    \             'a, 'b, 'c, 'd, 'e) t\n\
    \      val step0:\n\
    \         {combine: 'accum1 * 'input2 -> 'accum2,\n\
    \          input: 'input1}\n\
    \         -> ('input1, 'accum1, 'input2, 'accum2,\n\
    \             'a, 'b, 'c, 'd, 'e, 'f) step0\n\
    \      val step1:\n\
    \         {combine: 'accum1 * 'input -> 'accum2}\n\
    \         -> ('accum1, 'input, 'accum2,\n\
    \             'a, 'b, 'c, 'd, 'e, 'f, 'g) step1\n\
    \   end\n\
    \structure Fold01N: FOLD_01N =\n\
    \   struct\n\
    \      open Fold01N\n\
    \      fun fold {finish, start, zero} =\n\
    \         Fold.fold ((fn a => a, finish, fn () => zero, start),\n\
    \                    fn (finish, _, p, _) => finish (p ()))\n\
    \      fun step0 {combine, input} =\n\
    \         Fold.step0 (fn (_, finish, _, f) =>\n\
    \                     (finish,\n\
    \                      finish,\n\
    \                      fn () => f input,\n\
    \                      fn x' => combine (f input, x')))\n\
    \      fun step1 {combine} z input =\n\
    \         step0 {combine = combine, input = input} z\n\
    \   end\n"

  val t =
    FilesData {depends = [FoldFile.t], data = data, fileName = "Fold01N.sml"}
end

structure PrintfFile =
struct
  val data =
    "structure Printf =\n\
    \  struct\n\
    \     fun fprintf out =\n\
    \        Fold.fold ((out, fn a => a), fn (_, f) => f (fn p => p ()) ignore)\n\
    \     val printf = fn z => fprintf TextIO.stdOut z\n\
    \     fun one ((out, f), make) =\n\
    \        (out, fn r =>\n\
    \         f (fn p =>\n\
    \            make (fn s =>\n\
    \                  r (fn () => (p (); TextIO.output (out, s))))))\n\
    \     val ` =\n\
    \        fn z => Fold.step1 (fn (s, x) => one (x, fn f => f s)) z\n\
    \     fun spec to = Fold.step0 (fn x => one (x, fn f => f o to))\n\
    \     val B = fn z => spec Bool.toString z\n\
    \     val I = fn z => spec Int.toString z\n\
    \     val R = fn z => spec Real.toString z\n\
    \  end\n"

  val t =
    FilesData {depends = [FoldFile.t], data = data, fileName = "Printf.sml"}
end

structure ProductFile =
struct
  val data =
    "structure Product = struct\n\
    \  datatype ('a, 'b) product = & of 'a * 'b\n\
    \  type ('a, 'b) t = ('a, 'b) product\n\
    \  infix &\n\
    \end\n"

  val t = FilesData {depends = [], data = data, fileName = "Product.sml"}
end

structure OptionalArgFile =
struct
  val data =
    "structure OptionalArg =\n\
    \  struct\n\
    \     infix &\n\
    \     open Product\n\
    \     val make =\n\
    \        fn z =>\n\
    \        Fold.fold\n\
    \        ((fn a => a, fn (f, x) => f x),\n\
    \         fn (d, r) => fn func =>\n\
    \         Fold.fold ((fn a => a, d ()), fn (f, d) =>\n\
    \                    let\n\
    \                       val d & () = r (fn a => a, f d)\n\
    \                    in\n\
    \                       func d\n\
    \                    end))\n\
    \        z\n\
    \     fun D d = Fold.step0 (fn (f, r) =>\n\
    \                           (fn ds => f (d & ds),\n\
    \                            fn (f, a & b) => r (fn x => f a & x, b)))\n\
    \     val ` =\n\
    \        fn z =>\n\
    \        Fold.step1 (fn (x, (f, _ & d)) => (fn d => f (x & d), d))\n\
    \        z\n\
    \  end\n"

  val t =
    FilesData
      { depends = [FoldFile.t, ProductFile.t]
      , data = data
      , fileName = "OptionalArg.sml"
      }
end
