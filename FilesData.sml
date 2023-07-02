datatype files_data =
  FilesData of {depends: files_data list, data: string, fileName: string}

structure FoldFile =
struct
  val data =
    "structure Fold =\n\
    \struct\n\
    \  fun fold (a, f) g = g (a, f)\n\
    \  fun post (w, g) s =\n\
    \    w (fn (a, h) => s (a, g o h))\n\
    \  fun step0 h (a, f) =\n\
    \    fold (h a, f)\n\
    \  fun step1 h (a, f) b =\n\
    \    fold (h (b, a), f)\n\
    \  fun step2 h (a, f) b c =\n\
    \    fold (h (b, c, a), f)\n\
    \end\n\
    \fun $ (a, f) = f a\n"

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
