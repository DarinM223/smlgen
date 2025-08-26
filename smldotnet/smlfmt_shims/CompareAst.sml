(** Copyright (c) 2023 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure CompareAst:
sig
  val equal: {tabWidth: int} -> Ast.t * Ast.t -> bool
end =
struct

  (* =======================================================================
   * combinators for functions of type 'a * 'a -> bool (equality checkers)
   *
   * makes it a bit easier to write equality checks over records with this
   * idiom:
   *
   *   val checker =
   *     at #field1 eq1 <&>
   *     at #field2 eq2 <&>
   *     ...            <&>
   *     at #fieldN eqN
   *
   *   val result = checker (x, y)
   *)

  type 'a eq = 'a * 'a -> bool

  fun at (select: 'b -> 'a) (eq: 'a eq) : 'b eq =
    fn (x: 'b, y: 'b) => eq (select x, select y)

  fun <&> (eq1: 'a eq, eq2: 'a eq) : 'a eq =
    fn (x, y) => eq1 (x, y) andalso eq2 (x, y)

  infix 2 <&>

  (* ======================================================================= *)

  fun equal_op eq (op1, op2) =
    case (op1, op2) of
      (SOME x, SOME y) => eq (x, y)
    | (NONE, NONE) => true
    | _ => false

  (* ======================================================================= *)

  open Ast


  fun equal {tabWidth: int} (Ast tops1, Ast tops2) =
    let

      fun equal_tok (t1, t2) =
        Token.sameExceptForMultilineIndentation {tabWidth = tabWidth} (t1, t2)


      fun equal_syntaxseq eq (s1, s2) =
        case (s1, s2) of
          (SyntaxSeq.Empty, SyntaxSeq.Empty) => true
        | (SyntaxSeq.One x, SyntaxSeq.One y) => eq (x, y)
        | (SyntaxSeq.Many x, SyntaxSeq.Many y) =>
            (at #left equal_tok <&> at #elems (Seq.equal eq)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (x, y)
        | _ => false


      fun equal_ty (t1, t2) =
        case (t1, t2) of
          (Ty.Var v1, Ty.Var v2) => equal_tok (v1, v2)

        | (Ty.Record r1, Ty.Record r2) =>
            (at #left equal_tok <&> at #right equal_tok
             <&> at #delims (Seq.equal equal_tok)
             <&>
             at #elems (Seq.equal
               (at #lab equal_tok <&> at #colon equal_tok <&> at #ty equal_ty)))
              (r1, r2)

        | (Ty.Tuple t1, Ty.Tuple t2) =>
            (at #elems (Seq.equal equal_ty) <&> at #delims (Seq.equal equal_tok))
              (t1, t2)

        | (Ty.Con c1, Ty.Con c2) =>
            (at #args (equal_syntaxseq equal_ty)
             <&> at #id (at MaybeLongToken.getToken equal_tok)) (c1, c2)

        | (Ty.Arrow a1, Ty.Arrow a2) =>
            (at #from equal_ty <&> at #arrow equal_tok <&> at #to equal_ty)
              (a1, a2)

        | (Ty.Parens p1, Ty.Parens p2) =>
            (at #left equal_tok <&> at #ty equal_ty <&> at #right equal_tok)
              (p1, p2)

        | _ => false


      fun equal_patrow (r1, r2) =
        case (r1, r2) of
          (Pat.DotDotDot d1, Pat.DotDotDot d2) => equal_tok (d1, d2)

        | (Pat.LabEqPat lep1, Pat.LabEqPat lep2) =>
            (at #lab equal_tok <&> at #eq equal_tok <&> at #pat equal_pat)
              (lep1, lep2)

        | (Pat.LabAsPat lap1, Pat.LabAsPat lap2) =>
            (at #id equal_tok
             <&> at #ty (equal_op (at #colon equal_tok <&> at #ty equal_ty))
             <&> at #aspat (equal_op (at #ass equal_tok <&> at #pat equal_pat)))
              (lap1, lap2)

        | _ => false


      and equal_pat (p1, p2) =
        case (p1, p2) of
          (Pat.Wild w1, Pat.Wild w2) => equal_tok (w1, w2)

        | (Pat.Const c1, Pat.Const c2) => equal_tok (c1, c2)

        | (Pat.Unit u1, Pat.Unit u2) =>
            (at #left equal_tok <&> at #right equal_tok) (u1, u2)

        | (Pat.Ident i1, Pat.Ident i2) =>
            (at #opp (equal_op equal_tok)
             <&> at #id (at MaybeLongToken.getToken equal_tok)) (i1, i2)

        | (Pat.List l1, Pat.List l2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_pat)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (l1, l2)

        | (Pat.Tuple t1, Pat.Tuple t2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_pat)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (t1, t2)

        | (Pat.Record r1, Pat.Record r2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_patrow)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (r1, r2)

        | (Pat.Parens p1, Pat.Parens p2) =>
            (at #left equal_tok <&> at #pat equal_pat <&> at #right equal_tok)
              (p1, p2)

        | (Pat.Con c1, Pat.Con c2) =>
            (at #opp (equal_op equal_tok)
             <&> at #id (at MaybeLongToken.getToken equal_tok)
             <&> at #atpat equal_pat) (c1, c2)

        | (Pat.Infix i1, Pat.Infix i2) =>
            (at #left equal_pat <&> at #id equal_tok <&> at #right equal_pat)
              (i1, i2)

        | (Pat.Typed t1, Pat.Typed t2) =>
            (at #pat equal_pat <&> at #colon equal_tok <&> at #ty equal_ty)
              (t1, t2)

        | (Pat.Layered l1, Pat.Layered l2) =>
            (at #opp (equal_op equal_tok) <&> at #id equal_tok
             <&> at #ty (equal_op (at #colon equal_tok <&> at #ty equal_ty))
             <&> at #ass equal_tok <&> at #pat equal_pat) (l1, l2)

        | (Pat.Or o1, Pat.Or o2) =>
            (at #elems (Seq.equal equal_pat)
             <&> at #delims (Seq.equal equal_tok)) (o1, o2)

        | _ => false


      fun equal_rowexp (re1, re2) =
        case (re1, re2) of
          (Exp.RecordRow r1, Exp.RecordRow r2) =>
            (at #lab equal_tok <&> at #eq equal_tok <&> at #exp equal_exp)
              (r1, r2)

        | (Exp.RecordPun p1, Exp.RecordPun p2) => at #id equal_tok (p1, p2)

        | _ => false


      and equal_exp (e1, e2) =
        case (e1, e2) of
          (Exp.Const c1, Exp.Const c2) => equal_tok (c1, c2)

        | (Exp.Ident i1, Exp.Ident i2) =>
            (at #opp (equal_op equal_tok)
             <&> at #id (at MaybeLongToken.getToken equal_tok)) (i1, i2)

        | (Exp.Record r1, Exp.Record r2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_rowexp)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (r1, r2)

        | (Exp.Select s1, Exp.Select s2) =>
            (at #hash equal_tok <&> at #label equal_tok) (s1, s2)

        | (Exp.Unit u1, Exp.Unit u2) =>
            (at #left equal_tok <&> at #right equal_tok) (u1, u2)

        | (Exp.Tuple t1, Exp.Tuple t2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_exp)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (t1, t2)

        | (Exp.List l1, Exp.List l2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_exp)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (l1, l2)

        | (Exp.Sequence s1, Exp.Sequence s2) =>
            (at #left equal_tok <&> at #elems (Seq.equal equal_exp)
             <&> at #delims (Seq.equal equal_tok) <&> at #right equal_tok)
              (s1, s2)

        | (Exp.LetInEnd lie1, Exp.LetInEnd lie2) =>
            (at #lett equal_tok <&> at #dec equal_dec <&> at #inn equal_tok
             <&> at #exps (Seq.equal equal_exp)
             <&> at #delims (Seq.equal equal_tok) <&> at #endd equal_tok)
              (lie1, lie2)

        | (Exp.Parens p1, Exp.Parens p2) =>
            (at #left equal_tok <&> at #exp equal_exp <&> at #right equal_tok)
              (p1, p2)

        | (Exp.App a1, Exp.App a2) =>
            (at #left equal_exp <&> at #right equal_exp) (a1, a2)

        | (Exp.Infix i1, Exp.Infix i2) =>
            (at #left equal_exp <&> at #id equal_tok <&> at #right equal_exp)
              (i1, i2)

        | (Exp.Typed t1, Exp.Typed t2) =>
            (at #exp equal_exp <&> at #colon equal_tok <&> at #ty equal_ty)
              (t1, t2)

        | (Exp.Andalso a1, Exp.Andalso a2) =>
            (at #left equal_exp <&> at #andalsoo equal_tok
             <&> at #right equal_exp) (a1, a2)

        | (Exp.Orelse o1, Exp.Orelse o2) =>
            (at #left equal_exp <&> at #orelsee equal_tok
             <&> at #right equal_exp) (o1, o2)

        | (Exp.Handle h1, Exp.Handle h2) =>
            (at #exp equal_exp <&> at #handlee equal_tok
             <&>
             at #elems (Seq.equal
               (at #pat equal_pat <&> at #arrow equal_tok <&> at #exp equal_exp))
             <&> at #delims (Seq.equal equal_tok)
             <&> at #optbar (equal_op equal_tok)) (h1, h2)

        | (Exp.Raise r1, Exp.Raise r2) =>
            (at #raisee equal_tok <&> at #exp equal_exp) (r1, r2)

        | (Exp.IfThenElse ite1, Exp.IfThenElse ite2) =>
            (at #iff equal_tok <&> at #exp1 equal_exp <&> at #thenn equal_tok
             <&> at #exp2 equal_exp <&> at #elsee equal_tok
             <&> at #exp3 equal_exp) (ite1, ite2)

        | (Exp.While w1, Exp.While w2) =>
            (at #whilee equal_tok <&> at #exp1 equal_exp <&> at #doo equal_tok
             <&> at #exp2 equal_exp) (w1, w2)

        | (Exp.Case c1, Exp.Case c2) =>
            (at #casee equal_tok <&> at #exp equal_exp <&> at #off equal_tok
             <&>
             at #elems (Seq.equal
               (at #pat equal_pat <&> at #arrow equal_tok <&> at #exp equal_exp))
             <&> at #delims (Seq.equal equal_tok)
             <&> at #optbar (equal_op equal_tok)) (c1, c2)

        | (Exp.Fn f1, Exp.Fn f2) =>
            (at #fnn equal_tok
             <&>
             at #elems (Seq.equal
               (at #pat equal_pat <&> at #arrow equal_tok <&> at #exp equal_exp))
             <&> at #delims (Seq.equal equal_tok)
             <&> at #optbar (equal_op equal_tok)) (f1, f2)

        | (Exp.MLtonSpecific m1, Exp.MLtonSpecific m2) =>
            (at #underscore equal_tok <&> at #directive equal_tok
             <&> at #contents (Seq.equal equal_tok) <&> at #semicolon equal_tok)
              (m1, m2)

        | _ => false


      and equal_fnameargs (fna1, fna2) =
        case (fna1, fna2) of
          (Exp.PrefixedFun pf1, Exp.PrefixedFun pf2) =>
            (at #opp (equal_op equal_tok) <&> at #id equal_tok
             <&> at #args (Seq.equal equal_pat)) (pf1, pf2)

        | (Exp.InfixedFun if1, Exp.InfixedFun if2) =>
            (at #larg equal_pat <&> at #id equal_tok <&> at #rarg equal_pat)
              (if1, if2)

        | (Exp.CurriedInfixedFun cif1, Exp.CurriedInfixedFun cif2) =>
            (at #lparen equal_tok <&> at #larg equal_pat <&> at #id equal_tok
             <&> at #rarg equal_pat <&> at #rparen equal_tok
             <&> at #args (Seq.equal equal_pat)) (cif1, cif2)

        | _ => false


      and equal_fvalbind (fv1, fv2) =
        (at #delims (Seq.equal equal_tok)
         <&>
         at #elems (Seq.equal
           (at #delims (Seq.equal equal_tok) <&> at #optbar (equal_op equal_tok)
            <&>
            at #elems (Seq.equal
              (at #fname_args equal_fnameargs
               <&> at #ty (equal_op (at #colon equal_tok <&> at #ty equal_ty))
               <&> at #eq equal_tok <&> at #exp equal_exp))))) (fv1, fv2)


      and equal_typbind (tb1, tb2) =
        (at #elems (Seq.equal
           (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
            <&> at #eq equal_tok <&> at #ty equal_ty))
         <&> at #delims (Seq.equal equal_tok)) (tb1, tb2)


      and equal_datbind (db1, db2) =
        (at #delims (Seq.equal equal_tok)
         <&>
         at #elems (Seq.equal
           (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
            <&> at #eq equal_tok <&> at #optbar (equal_op equal_tok)
            <&> at #delims (Seq.equal equal_tok)
            <&>
            at #elems (Seq.equal
              (at #opp (equal_op equal_tok) <&> at #id equal_tok
               <&> at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty)))))))
          (db1, db2)


      and equal_dec (d1, d2) =
        case (d1, d2) of
          (Exp.DecEmpty, Exp.DecEmpty) => true

        | (Exp.DecVal v1, Exp.DecVal v2) =>
            (at #vall equal_tok <&> at #tyvars (equal_syntaxseq equal_tok)
             <&>
             at #elems (Seq.equal
               (at #recc (equal_op equal_tok) <&> at #pat equal_pat
                <&> at #eq equal_tok <&> at #exp equal_exp))
             <&> at #delims (Seq.equal equal_tok)) (v1, v2)

        | (Exp.DecFun f1, Exp.DecFun f2) =>
            (at #funn equal_tok <&> at #tyvars (equal_syntaxseq equal_tok)
             <&> at #fvalbind equal_fvalbind) (f1, f2)

        | (Exp.DecType t1, Exp.DecType t2) =>
            (at #typee equal_tok <&> at #typbind equal_typbind) (t1, t2)

        | (Exp.DecDatatype d1, Exp.DecDatatype d2) =>
            (at #datatypee equal_tok <&> at #datbind equal_datbind
             <&>
             at #withtypee (equal_op
               (at #withtypee equal_tok <&> at #typbind equal_typbind)))
              (d1, d2)

        | (Exp.DecReplicateDatatype rd1, Exp.DecReplicateDatatype rd2) =>
            (at #left_datatypee equal_tok <&> at #left_id equal_tok
             <&> at #eq equal_tok <&> at #right_datatypee equal_tok
             <&> at #right_id (at MaybeLongToken.getToken equal_tok)) (rd1, rd2)

        | (Exp.DecAbstype a1, Exp.DecAbstype a2) =>
            (at #abstypee equal_tok <&> at #datbind equal_datbind
             <&>
             at #withtypee (equal_op
               (at #withtypee equal_tok <&> at #typbind equal_typbind))
             <&> at #withh equal_tok <&> at #dec equal_dec
             <&> at #endd equal_tok) (a1, a2)

        | (Exp.DecException e1, Exp.DecException e2) =>
            (at #exceptionn equal_tok <&> at #elems (Seq.equal equal_exbind)
             <&> at #delims (Seq.equal equal_tok)) (e1, e2)

        | (Exp.DecLocal l1, Exp.DecLocal l2) =>
            (at #locall equal_tok <&> at #left_dec equal_dec
             <&> at #inn equal_tok <&> at #right_dec equal_dec
             <&> at #endd equal_tok) (l1, l2)

        | (Exp.DecOpen o1, Exp.DecOpen o2) =>
            (at #openn equal_tok
             <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok)))
              (o1, o2)

        | (Exp.DecMultiple m1, Exp.DecMultiple m2) =>
            (at #elems (Seq.equal equal_dec)
             <&> at #delims (Seq.equal (equal_op equal_tok))) (m1, m2)

        | (Exp.DecInfix i1, Exp.DecInfix i2) =>
            (at #infixx equal_tok <&> at #precedence (equal_op equal_tok)
             <&> at #elems (Seq.equal equal_tok)) (i1, i2)

        | (Exp.DecInfixr i1, Exp.DecInfixr i2) =>
            (at #infixrr equal_tok <&> at #precedence (equal_op equal_tok)
             <&> at #elems (Seq.equal equal_tok)) (i1, i2)

        | (Exp.DecNonfix n1, Exp.DecNonfix n2) =>
            (at #nonfixx equal_tok <&> at #elems (Seq.equal equal_tok)) (n1, n2)

        | _ => false


      and equal_exbind (b1, b2) =
        case (b1, b2) of
          (Exp.ExnNew n1, Exp.ExnNew n2) =>
            (at #opp (equal_op equal_tok) <&> at #id equal_tok
             <&> at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty)))
              (n1, n2)

        | (Exp.ExnReplicate r1, Exp.ExnReplicate r2) =>
            (at #opp (equal_op equal_tok) <&> at #left_id equal_tok
             <&> at #eq equal_tok
             <&> at #right_id (at MaybeLongToken.getToken equal_tok)) (r1, r2)

        | _ => false


      fun equal_sigdec (Sig.Signature s1, Sig.Signature s2) =
        (at #signaturee equal_tok <&> at #delims (Seq.equal equal_tok)
         <&>
         at #elems (Seq.equal
           (at #ident equal_tok <&> at #eq equal_tok <&> at #sigexp equal_sigexp)))
          (s1, s2)


      and equal_sigexp (se1, se2) =
        case (se1, se2) of
          (Sig.Ident i1, Sig.Ident i2) => equal_tok (i1, i2)

        | (Sig.Spec s1, Sig.Spec s2) =>
            (at #sigg equal_tok <&> at #spec equal_spec <&> at #endd equal_tok)
              (s1, s2)

        | (Sig.WhereType w1, Sig.WhereType w2) =>
            (at #sigexp equal_sigexp
             <&>
             at #elems (Seq.equal
               (at #wheree equal_tok <&> at #typee equal_tok
                <&> at #tyvars (equal_syntaxseq equal_tok)
                <&> at #tycon (at MaybeLongToken.getToken equal_tok)
                <&> at #eq equal_tok <&> at #ty equal_ty))) (w1, w2)

        | _ => false


      and equal_spec (s1, s2) =
        case (s1, s2) of
          (Sig.EmptySpec, Sig.EmptySpec) => true

        | (Sig.Val v1, Sig.Val v2) =>
            (at #vall equal_tok
             <&>
             at #elems (Seq.equal
               (at #vid equal_tok <&> at #colon equal_tok <&> at #ty equal_ty))
             <&> at #delims (Seq.equal equal_tok)) (v1, v2)

        | (Sig.Type t1, Sig.Type t2) =>
            (at #typee equal_tok
             <&>
             at #elems (Seq.equal
               (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok))
             <&> at #delims (Seq.equal equal_tok)) (t1, t2)

        | (Sig.TypeAbbreviation a1, Sig.TypeAbbreviation a2) =>
            (at #typee equal_tok <&> at #typbind equal_typbind) (a1, a2)

        | (Sig.Eqtype e1, Sig.Eqtype e2) =>
            (at #eqtypee equal_tok
             <&>
             at #elems (Seq.equal
               (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok))
             <&> at #delims (Seq.equal equal_tok)) (e1, e2)

        | (Sig.Datatype d1, Sig.Datatype d2) =>
            (at #datatypee equal_tok <&> at #delims (Seq.equal equal_tok)
             <&>
             at #elems (Seq.equal
               (at #tyvars (equal_syntaxseq equal_tok) <&> at #tycon equal_tok
                <&> at #eq equal_tok <&> at #optbar (equal_op equal_tok)
                <&> at #delims (Seq.equal equal_tok)
                <&>
                at #elems (Seq.equal
                  (at #vid equal_tok
                   <&>
                   at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty)))))))
              (d1, d2)

        | (Sig.ReplicateDatatype r1, Sig.ReplicateDatatype r2) =>
            (at #left_datatypee equal_tok <&> at #left_id equal_tok
             <&> at #eq equal_tok <&> at #right_datatypee equal_tok
             <&> at #right_id (at MaybeLongToken.getToken equal_tok)) (r1, r2)

        | (Sig.Exception e1, Sig.Exception e2) =>
            (at #exceptionn equal_tok <&> at #delims (Seq.equal equal_tok)
             <&>
             at #elems (Seq.equal
               (at #vid equal_tok
                <&> at #arg (equal_op (at #off equal_tok <&> at #ty equal_ty)))))
              (e1, e2)

        | (Sig.Structure s1, Sig.Structure s2) =>
            (at #structuree equal_tok <&> at #delims (Seq.equal equal_tok)
             <&>
             at #elems (Seq.equal
               (at #id equal_tok <&> at #colon equal_tok
                <&> at #sigexp equal_sigexp))) (s1, s2)

        | (Sig.Include i1, Sig.Include i2) =>
            (at #includee equal_tok <&> at #sigexp equal_sigexp) (i1, i2)

        | (Sig.IncludeIds i1, Sig.IncludeIds i2) =>
            (at #includee equal_tok <&> at #sigids (Seq.equal equal_tok))
              (i1, i2)

        | (Sig.SharingType s1, Sig.SharingType s2) =>
            (at #spec equal_spec <&> at #sharingg equal_tok
             <&> at #typee equal_tok
             <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
             <&> at #delims (Seq.equal equal_tok)) (s1, s2)

        | (Sig.Sharing s1, Sig.Sharing s2) =>
            (at #spec equal_spec <&> at #sharingg equal_tok
             <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
             <&> at #delims (Seq.equal equal_tok)) (s1, s2)

        | (Sig.Multiple m1, Sig.Multiple m2) =>
            (at #elems (Seq.equal equal_spec)
             <&> at #delims (Seq.equal (equal_op equal_tok))) (m1, m2)

        | _ => false


      fun equal_strdec (sd1, sd2) =
        case (sd1, sd2) of
          (Str.DecEmpty, Str.DecEmpty) => true

        | (Str.DecCore d1, Str.DecCore d2) => equal_dec (d1, d2)

        | (Str.DecStructure s1, Str.DecStructure s2) =>
            (at #structuree equal_tok <&> at #delims (Seq.equal equal_tok)
             <&>
             at #elems (Seq.equal
               (at #strid equal_tok
                <&>
                at #constraint (equal_op
                  (at #colon equal_tok <&> at #sigexp equal_sigexp))
                <&> at #eq equal_tok <&> at #strexp equal_strexp))) (s1, s2)

        | (Str.DecMultiple m1, Str.DecMultiple m2) =>
            (at #elems (Seq.equal equal_strdec)
             <&> at #delims (Seq.equal (equal_op equal_tok))) (m1, m2)

        | (Str.DecLocalInEnd lie1, Str.DecLocalInEnd lie2) =>
            (at #locall equal_tok <&> at #strdec1 equal_strdec
             <&> at #inn equal_tok <&> at #strdec2 equal_strdec
             <&> at #endd equal_tok) (lie1, lie2)

        | (Str.MLtonOverload o1, Str.MLtonOverload o2) =>
            (at #underscore equal_tok <&> at #overload equal_tok
             <&> at #prec equal_tok <&> at #name equal_tok
             <&> at #colon equal_tok <&> at #colon equal_tok <&> at #ty equal_ty
             <&> at #ass equal_tok
             <&> at #elems (Seq.equal (at MaybeLongToken.getToken equal_tok))
             <&> at #delims (Seq.equal equal_tok)) (o1, o2)

        | _ => false


      and equal_strexp (se1, se2) =
        case (se1, se2) of
          (Str.Ident i1, Str.Ident i2) =>
            at MaybeLongToken.getToken equal_tok (i1, i2)

        | (Str.Struct s1, Str.Struct s2) =>
            (at #structt equal_tok <&> at #strdec equal_strdec
             <&> at #endd equal_tok) (s1, s2)

        | (Str.Constraint c1, Str.Constraint c2) =>
            (at #strexp equal_strexp <&> at #colon equal_tok
             <&> at #sigexp equal_sigexp) (c1, c2)

        | (Str.FunAppExp e1, Str.FunAppExp e2) =>
            (at #funid equal_tok <&> at #lparen equal_tok
             <&> at #strexp equal_strexp <&> at #rparen equal_tok) (e1, e2)

        | (Str.FunAppDec d1, Str.FunAppDec d2) =>
            (at #funid equal_tok <&> at #lparen equal_tok
             <&> at #strdec equal_strdec <&> at #rparen equal_tok) (d1, d2)

        | (Str.LetInEnd lie1, Str.LetInEnd lie2) =>
            (at #lett equal_tok <&> at #strdec equal_strdec
             <&> at #inn equal_tok <&> at #strexp equal_strexp
             <&> at #endd equal_tok) (lie1, lie2)

        | _ => false


      fun equal_fundec (Fun.DecFunctor x, Fun.DecFunctor y) =
        let
          fun equal_funarg (fa1, fa2) =
            case (fa1, fa2) of
              (Fun.ArgSpec s1, Fun.ArgSpec s2) => equal_spec (s1, s2)

            | (Fun.ArgIdent i1, Fun.ArgIdent i2) =>
                (at #strid equal_tok <&> at #colon equal_tok
                 <&> at #sigexp equal_sigexp) (i1, i2)

            | _ => false
        in

          (at #functorr equal_tok <&> at #delims (Seq.equal equal_tok)
           <&>
           at #elems (Seq.equal
             (at #funid equal_tok <&> at #lparen equal_tok
              <&> at #funarg equal_funarg <&> at #rparen equal_tok
              <&>
              at #constraint (equal_op
                (at #colon equal_tok <&> at #sigexp equal_sigexp))
              <&> at #eq equal_tok <&> at #strexp equal_strexp))) (x, y)
        end


      fun equal_topdec (td1, td2) =
        case (td1, td2) of
          (SigDec sd1, SigDec sd2) => equal_sigdec (sd1, sd2)
        | (StrDec sd1, StrDec sd2) => equal_strdec (sd1, sd2)
        | (FunDec fd1, FunDec fd2) => equal_fundec (fd1, fd2)
        | (TopExp te1, TopExp te2) =>
            (at #exp equal_exp <&> at #semicolon equal_tok) (te1, te2)
        | _ => false

    in
      Seq.equal (at #topdec equal_topdec <&> at #semicolon (equal_op equal_tok))
        (tops1, tops2)
    end

end
