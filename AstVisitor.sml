structure AstVisitor =
struct
  type withtypee = {withtypee: Token.t, typbind: Ast.Exp.typbind} option
  type 'a visitor =
    { state: 'a
    , goDecType: 'a * Ast.Exp.dec * Ast.Exp.typbind -> Ast.Exp.dec
    , goDecReplicateDatatype: 'a * Ast.Exp.dec * Token.t * MaybeLongToken.t
      -> Ast.Exp.dec
    , goDecDatatype: 'a * Ast.Exp.dec * Ast.Exp.datbind * withtypee
      -> Ast.Exp.dec
    , onStructure: Token.t -> 'a -> 'a
    , onFunctor: Token.t -> 'a -> 'a
    }
  fun updateVisitor r =
    let
      fun from state goDecType goDecReplicateDatatype goDecDatatype onStructure
        onFunctor =
        { state = state
        , goDecType = goDecType
        , goDecReplicateDatatype = goDecReplicateDatatype
        , goDecDatatype = goDecDatatype
        , onStructure = onStructure
        , onFunctor = onFunctor
        }
      fun to ?
        { state
        , goDecType
        , goDecReplicateDatatype
        , goDecDatatype
        , onStructure
        , onFunctor
        } =
        ?state goDecType goDecReplicateDatatype goDecDatatype onStructure
          onFunctor
    in
      FunctionalRecordUpdate.makeUpdate6 (from, from, to) r
    end

  fun goExp 0 (_: 'a visitor) (exp: Ast.Exp.exp) = exp
    | goExp _ _ (Ast.Exp.Const tok) = Ast.Exp.Const tok
    | goExp _ _ (Ast.Exp.Ident r) = Ast.Exp.Ident r
    | goExp n visitor (Ast.Exp.Record {left, elems, delims, right}) =
        Ast.Exp.Record
          { left = left
          , elems =
              Seq.map
                (fn Ast.Exp.RecordPun r => Ast.Exp.RecordPun r
                  | Ast.Exp.RecordRow {lab, eq, exp} =>
                   Ast.Exp.RecordRow
                     {lab = lab, eq = eq, exp = goExp (n - 1) visitor exp})
                elems
          , delims = delims
          , right = right
          }
    | goExp _ _ (Ast.Exp.Select r) = Ast.Exp.Select r
    | goExp _ _ (Ast.Exp.Unit r) = Ast.Exp.Unit r
    | goExp n visitor (Ast.Exp.Tuple {left, elems, delims, right}) =
        Ast.Exp.Tuple
          { left = left
          , elems = Seq.map (goExp (n - 1) visitor) elems
          , delims = delims
          , right = right
          }
    | goExp n visitor (Ast.Exp.List {left, elems, delims, right}) =
        Ast.Exp.List
          { left = left
          , elems = Seq.map (goExp (n - 1) visitor) elems
          , delims = delims
          , right = right
          }
    | goExp n visitor (Ast.Exp.Parens {left, exp, right}) =
        Ast.Exp.Parens
          {left = left, exp = goExp (n - 1) visitor exp, right = right}
    | goExp n visitor (Ast.Exp.Sequence {left, elems, delims, right}) =
        Ast.Exp.Sequence
          { left = left
          , elems = Seq.map (goExp (n - 1) visitor) elems
          , delims = delims
          , right = right
          }
    | goExp n visitor (Ast.Exp.App {left, right}) =
        Ast.Exp.App
          { left = goExp (n - 1) visitor left
          , right = goExp (n - 1) visitor right
          }
    | goExp n visitor (Ast.Exp.Infix {left, id, right}) =
        Ast.Exp.Infix
          { left = goExp (n - 1) visitor left
          , id = id
          , right = goExp (n - 1) visitor right
          }
    | goExp n visitor (Ast.Exp.Typed {exp, colon, ty}) =
        Ast.Exp.Typed {exp = goExp (n - 1) visitor exp, colon = colon, ty = ty}
    | goExp n visitor (Ast.Exp.Andalso {left, andalsoo, right}) =
        Ast.Exp.Andalso
          { left = goExp (n - 1) visitor left
          , andalsoo = andalsoo
          , right = goExp (n - 1) visitor right
          }
    | goExp n visitor (Ast.Exp.Orelse {left, orelsee, right}) =
        Ast.Exp.Orelse
          { left = goExp (n - 1) visitor left
          , orelsee = orelsee
          , right = goExp (n - 1) visitor right
          }
    | goExp n visitor (Ast.Exp.Handle {exp, handlee, elems, delims, optbar}) =
        Ast.Exp.Handle
          { exp = goExp (n - 1) visitor exp
          , handlee = handlee
          , elems =
              Seq.map
                (fn {pat, arrow, exp} =>
                   {pat = pat, arrow = arrow, exp = goExp (n - 1) visitor exp})
                elems
          , delims = delims
          , optbar = optbar
          }
    | goExp n visitor (Ast.Exp.Raise {raisee, exp}) =
        Ast.Exp.Raise {raisee = raisee, exp = goExp (n - 1) visitor exp}
    | goExp n visitor (Ast.Exp.IfThenElse {iff, exp1, thenn, exp2, elsee, exp3}) =
        Ast.Exp.IfThenElse
          { iff = iff
          , exp1 = goExp (n - 1) visitor exp1
          , thenn = thenn
          , exp2 = goExp (n - 1) visitor exp2
          , elsee = elsee
          , exp3 = goExp (n - 1) visitor exp3
          }
    | goExp n visitor (Ast.Exp.While {whilee, exp1, doo, exp2}) =
        Ast.Exp.While
          { whilee = whilee
          , exp1 = goExp (n - 1) visitor exp1
          , doo = doo
          , exp2 = goExp (n - 1) visitor exp2
          }
    | goExp n visitor (Ast.Exp.Case {casee, exp, off, elems, delims, optbar}) =
        Ast.Exp.Case
          { casee = casee
          , exp = goExp (n - 1) visitor exp
          , off = off
          , elems =
              Seq.map
                (fn {pat, arrow, exp} =>
                   {pat = pat, arrow = arrow, exp = goExp (n - 1) visitor exp})
                elems
          , delims = delims
          , optbar = optbar
          }
    | goExp n visitor (Ast.Exp.Fn {fnn, elems, delims, optbar}) =
        Ast.Exp.Fn
          { fnn = fnn
          , elems =
              Seq.map
                (fn {pat, arrow, exp} =>
                   {pat = pat, arrow = arrow, exp = goExp (n - 1) visitor exp})
                elems
          , delims = delims
          , optbar = optbar
          }
    | goExp n visitor (Ast.Exp.LetInEnd {lett, dec, inn, exps, delims, endd}) =
        Ast.Exp.LetInEnd
          { lett = lett
          , dec = goDec (n - 1) visitor dec
          , inn = inn
          , exps = Seq.map (goExp (n - 1) visitor) exps
          , delims = delims
          , endd = endd
          }
    | goExp _ _ (Ast.Exp.MLtonSpecific r) = Ast.Exp.MLtonSpecific r
  and goDec n (visitor: 'a visitor) (dec: Ast.Exp.dec) =
    case dec of
      Ast.Exp.DecEmpty => dec
    | Ast.Exp.DecVal {vall, tyvars, elems, delims} =>
        Ast.Exp.DecVal
          { vall = vall
          , tyvars = tyvars
          , elems =
              Seq.map
                (fn {recc, pat, eq, exp} =>
                   {recc = recc, pat = pat, eq = eq, exp = goExp n visitor exp})
                elems
          , delims = delims
          }
    | Ast.Exp.DecFun {funn, tyvars, fvalbind = {elems, delims}} =>
        Ast.Exp.DecFun
          { funn = funn
          , tyvars = tyvars
          , fvalbind =
              { elems =
                  Seq.map
                    (fn {elems, delims, optbar} =>
                       { elems =
                           Seq.map
                             (fn {fname_args, ty, eq, exp} =>
                                { fname_args = fname_args
                                , ty = ty
                                , eq = eq
                                , exp = goExp n visitor exp
                                }) elems
                       , delims = delims
                       , optbar = optbar
                       }) elems
              , delims = delims
              }
          }
    | Ast.Exp.DecType {typbind, ...} =>
        #goDecType visitor (#state visitor, dec, typbind)
    | Ast.Exp.DecDatatype {datbind, withtypee, ...} =>
        #goDecDatatype visitor (#state visitor, dec, datbind, withtypee)
    | Ast.Exp.DecReplicateDatatype {left_id, right_id, ...} =>
        #goDecReplicateDatatype visitor (#state visitor, dec, left_id, right_id)
    | Ast.Exp.DecAbstype {abstypee, datbind, withtypee, withh, dec, endd} =>
        Ast.Exp.DecAbstype
          { abstypee = abstypee
          , datbind = datbind
          , withtypee = withtypee
          , withh = withh
          , dec = dec
          , endd = endd
          }
    | Ast.Exp.DecException _ => dec
    | Ast.Exp.DecLocal {locall, left_dec, inn, right_dec, endd} =>
        Ast.Exp.DecLocal
          { locall = locall
          , left_dec = goDec n visitor left_dec
          , inn = inn
          , right_dec = goDec n visitor right_dec
          , endd = endd
          }
    | Ast.Exp.DecOpen _ => dec
    | Ast.Exp.DecMultiple {elems, delims} =>
        Ast.Exp.DecMultiple
          {elems = Seq.map (goDec n visitor) elems, delims = delims}
    | Ast.Exp.DecInfix _ => dec
    | Ast.Exp.DecInfixr _ => dec
    | Ast.Exp.DecNonfix _ => dec
  and goStrExp (visitor: 'a visitor) exp =
    (case exp of
       Ast.Str.Ident _ => exp
     | Ast.Str.Struct {structt, strdec, endd} =>
         Ast.Str.Struct
           {structt = structt, strdec = goStrDec visitor strdec, endd = endd}
     | Ast.Str.Constraint {strexp, colon, sigexp} =>
         Ast.Str.Constraint
           {strexp = goStrExp visitor strexp, colon = colon, sigexp = sigexp}
     | Ast.Str.FunAppExp {funid, lparen, strexp, rparen} =>
         Ast.Str.FunAppExp
           { funid = funid
           , lparen = lparen
           , strexp = goStrExp visitor strexp
           , rparen = rparen
           }
     | Ast.Str.FunAppDec {funid, lparen, strdec, rparen} =>
         Ast.Str.FunAppDec
           { funid = funid
           , lparen = lparen
           , strdec = goStrDec visitor strdec
           , rparen = rparen
           }
     | Ast.Str.LetInEnd {lett, strdec, inn, strexp, endd} =>
         Ast.Str.LetInEnd
           { lett = lett
           , strdec = goStrDec visitor strdec
           , inn = inn
           , strexp = goStrExp visitor strexp
           , endd = endd
           })
  and goStrDec (visitor: 'a visitor) dec =
    case dec of
      Ast.Str.DecEmpty => dec
    | Ast.Str.DecCore dec =>
        Ast.Str.DecCore (goDec (! Options.maxExpDepth) visitor dec)
    | Ast.Str.DecStructure {structuree, elems, delims} =>
        let
          open Fold FunctionalRecordUpdate
          val go = fn {strid, constraint, eq, strexp} =>
            { strid = strid
            , constraint = constraint
            , eq = eq
            , strexp =
                goStrExp
                  (updateVisitor visitor upd #state (#onStructure visitor strid)
                     $) strexp
            }
        in
          Ast.Str.DecStructure
            {structuree = structuree, elems = Seq.map go elems, delims = delims}
        end
    | Ast.Str.DecMultiple {elems, delims} =>
        Ast.Str.DecMultiple
          {elems = Seq.map (goStrDec visitor) elems, delims = delims}
    | Ast.Str.DecLocalInEnd {locall, strdec1, inn, strdec2, endd} =>
        Ast.Str.DecLocalInEnd
          { locall = locall
          , strdec1 = goStrDec visitor strdec1
          , inn = inn
          , strdec2 = goStrDec visitor strdec2
          , endd = endd
          }
    | Ast.Str.MLtonOverload _ => dec
  and goFunDec (visitor: 'a visitor)
    (Ast.Fun.DecFunctor {functorr, elems, delims}) =
    let
      open Fold FunctionalRecordUpdate
      val go = fn {funid, lparen, funarg, rparen, constraint, eq, strexp} =>
        { funid = funid
        , lparen = lparen
        , funarg = funarg
        , rparen = rparen
        , constraint = constraint
        , eq = eq
        , strexp =
            goStrExp
              (updateVisitor visitor upd #state (#onFunctor visitor funid) $)
              strexp
        }
    in
      Ast.Fun.DecFunctor
        {functorr = functorr, elems = Seq.map go elems, delims = delims}
    end
  and goTopDec (visitor: 'a visitor) (dec: Ast.topdec) =
    case dec of
      Ast.SigDec _ => dec
    | Ast.StrDec dec => Ast.StrDec (goStrDec visitor dec)
    | Ast.FunDec dec => Ast.FunDec (goFunDec visitor dec)
    | Ast.TopExp {exp, semicolon} =>
        Ast.TopExp
          { exp = goExp (! Options.maxExpDepth) visitor exp
          , semicolon = semicolon
          }

  type datbind_visitor =
    { mapTy: Ast.Ty.ty -> Ast.Ty.ty
    , mapTycon: Token.t -> Token.t
    , mapConbind: Token.t -> Token.t
    }
  fun goDatbind (visitor: datbind_visitor) ({elems, delims}: Ast.Exp.datbind) =
    let
      fun goArg {off, ty} =
        {off = off, ty = #mapTy visitor ty}
      fun goElem {opp, id, arg} =
        {opp = opp, id = #mapConbind visitor id, arg = Option.map goArg arg}
      fun goCon {tyvars, tycon, eq, elems, delims, optbar} =
        { tyvars = tyvars
        , tycon = #mapTycon visitor tycon
        , eq = eq
        , elems = Seq.map goElem elems
        , delims = delims
        , optbar = optbar
        }
    in
      {delims = delims, elems = Seq.map goCon elems}
    end
end
