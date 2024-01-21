structure AstVisitor =
struct
  type withtypee = {withtypee: Token.t, typbind: Ast.Exp.typbind} option
  type 'a visitor =
    { state: 'a
    , goDecType: 'a * Ast.Exp.dec * Ast.Exp.typbind -> Ast.Exp.dec
    , goDecDatatype: 'a * Ast.Exp.dec * Ast.Exp.datbind * withtypee
      -> Ast.Exp.dec
    , onStructure: Token.t -> 'a -> 'a
    , onFunctor: Token.t -> 'a -> 'a
    }
  fun updateVisitor r =
    let
      fun from state goDecType goDecDatatype onStructure onFunctor =
        { state = state
        , goDecType = goDecType
        , goDecDatatype = goDecDatatype
        , onStructure = onStructure
        , onFunctor = onFunctor
        }
      fun to ? {state, goDecType, goDecDatatype, onStructure, onFunctor} =
        ?state goDecType goDecDatatype onStructure onFunctor
    in
      FunctionalRecordUpdate.makeUpdate5 (from, from, to) r
    end

  fun goExp (_: 'a visitor) (exp: Ast.Exp.exp) = exp
  and goDec (visitor: 'a visitor) (dec: Ast.Exp.dec) =
    case dec of
      Ast.Exp.DecEmpty => dec
    | Ast.Exp.DecVal _ => dec
    | Ast.Exp.DecFun _ => dec
    | Ast.Exp.DecType {typbind, ...} =>
        #goDecType visitor (#state visitor, dec, typbind)
    | Ast.Exp.DecDatatype {datbind, withtypee, ...} =>
        #goDecDatatype visitor (#state visitor, dec, datbind, withtypee)
    | Ast.Exp.DecReplicateDatatype _ => dec
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
          , left_dec = goDec visitor left_dec
          , inn = inn
          , right_dec = goDec visitor right_dec
          , endd = endd
          }
    | Ast.Exp.DecOpen _ => dec
    | Ast.Exp.DecMultiple {elems, delims} =>
        Ast.Exp.DecMultiple
          {elems = Seq.map (goDec visitor) elems, delims = delims}
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
    | Ast.Str.DecCore dec => Ast.Str.DecCore (goDec visitor dec)
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
        Ast.TopExp {exp = goExp visitor exp, semicolon = semicolon}
end
