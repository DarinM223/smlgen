structure ShowGen =
struct
  open BuildAst Utils

  fun tyPat (_: Ty.ty) : Pat.pat = raise Fail "typat"
  fun tyExp (_: Ty.ty) : Exp.exp = raise Fail "tyexp"

  fun genConstrs (constrs: constr list) : Exp.exp =
    let
      val tups =
        List.map
          (fn {arg = SOME {ty, ...}, id, ...} =>
             (conPat id (tyPat ty), tyExp ty)
            | {id, ...} => (Pat.Const id, Const id)) constrs
    in
      multFnExp tups
    end

  fun genTypebind ({elems, ...}: typbind) =
    let
      val decs =
        List.map
          (fn {ty, tycon, tyvars, ...} =>
             let
               val name = mkToken ("show" ^ capitalize (Token.toString tycon))
               val varsPat = destructTuplePat
                 (List.map (Pat.Const o mkTyVar) (syntaxSeqToList tyvars))
             in
               valDec (Pat.Const name) (singleFnExp varsPat
                 (singleFnExp (tyPat ty) (tyExp ty)))
             end) (ArraySlice.foldr (op::) [] elems)
    in
      multDec decs
    end

  fun genDatabind ({elems, ...}: datbind) =
    let
      val elems = ArraySlice.foldr (op::) [] elems
      val decs =
        List.map
          (fn {tycon, tyvars, elems, ...} =>
             let
               val elems = ArraySlice.foldr (op::) [] elems
               val name = mkToken ("show" ^ capitalize (Token.toString tycon))
               val tyvars =
                 List.map (Pat.Const o mkTyVar) (syntaxSeqToList tyvars)
               fun header exp =
                 case tyvars of
                   [] => exp
                 | _ => singleFnExp (destructTuplePat tyvars) exp
             in
               valDec (Pat.Const name) (header (genConstrs elems))
             end) elems
    in
      multDec decs
    end

  val gen = {genTypebind = genTypebind, genDatabind = genDatabind}
end
