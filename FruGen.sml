structure FruGen =
struct
  open Ast Ast.Exp TokenUtils

  fun genDecsForTy ty : (Token.token -> Ast.Exp.dec) list =
    case ty of
      Ast.Ty.Var _ => []
    | Ast.Ty.Record {elems, ...} =>
        let
          open BuildAst
          val elems = Seq.toList elems
          val elems' = (List.concat o List.map (genDecsForTy o #ty)) elems
          val fromTok = mkToken "from"
          val toTok = mkToken "to"
          val fTok = mkToken "?"
          val rTok = mkToken "r"
          val from =
            singleFunDec fromTok (List.map (Pat.Const o #lab) elems) (recordExp
              (List.map ((fn l => (l, Const l)) o #lab) elems))
          val to =
            singleFunDec toTok
              [Pat.Const fTok, destructRecordPat (List.map #lab elems)]
              (List.foldl (fn (exp, acc) => App {left = acc, right = exp})
                 (Const fTok) (List.map (Const o #lab) elems))
          fun f name =
            singleFunDec name [Pat.Const rTok]
              (singleLetExp (multDec [from, to]) (App
                 { left = App
                     { left = Const (mkToken
                         ("FunctionalRecordUpdate.makeUpdate"
                          ^ Int.toString (List.length elems)))
                     , right =
                         tupleExp [Const fromTok, Const fromTok, Const toTok]
                     }
                 , right = Const rTok
                 }))
        in
          f :: elems'
        end
    | Ast.Ty.Tuple {elems, ...} =>
        (List.concat o List.map genDecsForTy o Seq.toList) elems
    | Ast.Ty.Con {args, ...} =>
        (case args of
           Ast.SyntaxSeq.Empty => []
         | Ast.SyntaxSeq.One ty => genDecsForTy ty
         | Ast.SyntaxSeq.Many {elems, ...} =>
             (List.concat o List.map genDecsForTy o Seq.toList) elems)
    | Ast.Ty.Arrow {from, to, ...} => genDecsForTy from @ genDecsForTy to
    | Ast.Ty.Parens {ty, ...} => genDecsForTy ty

  fun genTypebind ({elems, ...}: Ast.Exp.typbind) =
    let
      val decs = List.concat
        (List.map
           (fn {tycon, ty, ...} =>
              let
                val c = ref 0
                val decs = List.rev (genDecsForTy ty)
                val decs =
                  if List.length decs > 1 then
                    List.map
                      (fn dec =>
                         (mkToken (Int.toString (!c before (c := !c + 1))), dec))
                      decs
                  else
                    List.map (fn dec => (mkToken "", dec)) decs
              in
                List.map (fn (t, dec) => (appendTokens tycon t, dec)) decs
              end) (Seq.toList elems))
    in
      BuildAst.multDec
        (List.map
           (fn (t, f) =>
              f (mkToken ("update" ^ (Utils.capitalize (Token.toString t)))))
           decs)
    end

  fun genDatabind ({elems, ...}: Ast.Exp.datbind) _ =
    let
      open Token
      val decs = List.concat
        (List.map
           (fn {elems, tycon, ...} =>
              let
                val constrDecs: (token * (token * (token -> dec)) list) list =
                  List.map
                    (fn {id, arg = SOME {ty, ...}, ...} =>
                       let
                         val c = ref 0
                         val decs = List.rev (genDecsForTy ty)
                         val decs =
                           if List.length decs > 1 then
                             List.map
                               (fn dec =>
                                  ( mkToken (Int.toString
                                      (!c before (c := !c + 1)))
                                  , dec
                                  )) decs
                           else
                             List.map (fn dec => (mkToken "", dec)) decs
                       in
                         (id, decs)
                       end
                      | {id, ...} => (id, [])) (Seq.toList elems)
              in
                List.map (fn (t, decs) => (appendTokens tycon t, decs))
                  (List.concat
                     (if List.length constrDecs > 1 then
                        List.map
                          (fn (constr, decs) =>
                             List.map
                               (fn (t, dec) => (appendTokens constr t, dec))
                               decs) constrDecs
                      else
                        List.map #2 constrDecs))
              end) (Seq.toList elems))
    in
      BuildAst.multDec
        (List.map
           (fn (t, f) =>
              f (mkToken ("update" ^ (Utils.capitalize (Token.toString t)))))
           decs)
    end

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
