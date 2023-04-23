(* Wanted syntax:
 *
 * smlgen foo.sml Ast.Str.strdec:g Parser.t:u Person.t:s
 *
 * g - Derive generic
 * u - Derive functional record update
 * s - Derive show
 * o - Derive ord
 * h - Derive hash
 * e - Derive equals
 *
 * Can combine them: Ast.t:gus
 * Will ask for each line number pattern matches
 * (so if Ast.Str.strdec appears multiple times you can choose which one to apply it to)
 *)

fun filterToken tokenString ((token' :: path, actions) :: xs) =
      if token' = tokenString then (path, actions) :: filterToken tokenString xs
      else filterToken tokenString xs
  | filterToken tokenString (_ :: xs) = filterToken tokenString xs
  | filterToken _ [] = []

fun getActions tokenString (([token'], actions) :: xs) =
      if token' = tokenString then SOME actions else getActions tokenString xs
  | getActions tokenString (_ :: xs) = getActions tokenString xs
  | getActions _ [] = NONE

val allows = AstAllows.make
  { topExp = true
  , optBar = true
  , recordPun = true
  , orPat = true
  , extendedText = true
  }

val pretty = PrettierPrintAst.pretty
  {ribbonFrac = 1.0, maxWidth = 80, tabWidth = 4, indent = 2, debug = false}

type gen =
  { genTypebind: Ast.Exp.typbind -> Ast.Exp.dec
  , genDatabind: Ast.Exp.datbind -> Ast.Exp.dec
  }

val emptyGen: gen =
  { genTypebind = fn _ => Ast.Exp.DecEmpty
  , genDatabind = fn _ => Ast.Exp.DecEmpty
  }

val showGen: gen =
  { genTypebind = fn _ => raise Fail "show"
  , genDatabind = fn _ => raise Fail "show"
  }
val ordGen: gen =
  { genTypebind = fn _ => raise Fail "ord"
  , genDatabind = fn _ => raise Fail "ord"
  }
val hashGen: gen =
  { genTypebind = fn _ => raise Fail "hash"
  , genDatabind = fn _ => raise Fail "hash"
  }
val equalsGen: gen =
  { genTypebind = fn _ => raise Fail "equals"
  , genDatabind = fn _ => raise Fail "equals"
  }

fun lookupGen #"g" = GenericGen.gen
  | lookupGen #"u" = FruGen.gen
  | lookupGen #"s" = showGen
  | lookupGen #"o" = ordGen
  | lookupGen #"h" = hashGen
  | lookupGen #"e" = equalsGen
  | lookupGen ch =
      raise Fail ("unknown lookup character: " ^ Char.toString ch)

fun combineDecs (Ast.Exp.DecMultiple {elems = elems1, delims = delims1})
      (Ast.Exp.DecMultiple {elems = elems2, delims = delims2}) =
      Ast.Exp.DecMultiple
        { elems = ArraySlice.full (Array.fromList
            (ArraySlice.foldr (op::) [] elems1
             @ ArraySlice.foldr (op::) [] elems2))
        , delims = ArraySlice.full (Array.fromList
            (ArraySlice.foldr (op::) [] delims1
             @ ArraySlice.foldr (op::) [] delims2))
        }
  | combineDecs (Ast.Exp.DecMultiple {elems, delims}) dec =
      Ast.Exp.DecMultiple
        { elems = ArraySlice.full (Array.fromList
            (ArraySlice.foldr (op::) [] elems @ [dec]))
        , delims = ArraySlice.full (Array.fromList
            (ArraySlice.foldr (op::) [] delims @ [NONE]))
        }
  | combineDecs dec (Ast.Exp.DecMultiple {elems, delims}) =
      Ast.Exp.DecMultiple
        { elems = ArraySlice.full (Array.fromList
            (dec :: ArraySlice.foldr (op::) [] elems))
        , delims = ArraySlice.full (Array.fromList
            (NONE :: ArraySlice.foldr (op::) [] delims))
        }
  | combineDecs dec1 dec2 =
      Ast.Exp.DecMultiple
        { elems = ArraySlice.full (Array.fromList [dec1, dec2])
        , delims = ArraySlice.full (Array.fromList [NONE, NONE])
        }

fun addGen (gen1: gen) (gen2: gen) : gen =
  { genTypebind = fn bind =>
      combineDecs (#genTypebind gen1 bind) (#genTypebind gen2 bind)
  , genDatabind = fn bind =>
      combineDecs (#genDatabind gen1 bind) (#genDatabind gen2 bind)
  }

local
  fun confirm default next =
    ( print "\nConfirm [y/n]? "
    ; case TextIO.inputLine TextIO.stdIn of
        NONE => default
      | SOME line =>
          let
            val line = String.map Char.toUpper line
          in
            if line = "Y\n" then next ()
            else if line = "N\n" then default
            else confirm default next
          end
    )
  fun printToken t =
    ( print (Token.toString t ^ ":")
    ; print
        (Int.toString (#line (Source.absoluteEnd (Token.getSource t))) ^ " ")
    )
  fun printDecTypes (Ast.Exp.DecType {typbind = {elems, ...}, ...}) =
        ArraySlice.app (fn e => printToken (#tycon e)) elems
    | printDecTypes (Ast.Exp.DecDatatype {datbind = {elems, ...}, ...}) =
        ArraySlice.app (fn e => printToken (#tycon e)) elems
    | printDecTypes _ = raise Fail "Unknown declaration type"
  fun goExp _ (exp: Ast.Exp.exp) = exp
  and goDec args (dec: Ast.Exp.dec) =
    case dec of
      Ast.Exp.DecEmpty => dec
    | Ast.Exp.DecVal _ => dec
    | Ast.Exp.DecFun _ => dec
    | Ast.Exp.DecType {typbind, ...} =>
        let
          val actions: gen option =
            (Option.join
             o Option.map (fn e => getActions (Token.toString (#tycon e)) args)
             o
             ArraySlice.find (fn e =>
               Option.isSome (getActions (Token.toString (#tycon e)) args))
             o #elems) typbind
        in
          case actions of
            SOME action =>
              ( print "Types: "
              ; printDecTypes dec
              ; confirm dec (fn () =>
                  combineDecs dec (#genTypebind action typbind))
              )
          | NONE => dec
        end
    | Ast.Exp.DecDatatype {datbind, ...} =>
        let
          val actions: gen option =
            (Option.join
             o Option.map (fn e => getActions (Token.toString (#tycon e)) args)
             o
             ArraySlice.find (fn e =>
               Option.isSome (getActions (Token.toString (#tycon e)) args))
             o #elems) datbind
        in
          case actions of
            SOME action =>
              ( print "Types: "
              ; printDecTypes dec
              ; confirm dec (fn () =>
                  combineDecs dec (#genDatabind action datbind))
              )
          | NONE => dec
        end
    | Ast.Exp.DecReplicateDatatype {left_datatypee, right_datatypee, ...} => dec
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
          , left_dec = goDec args left_dec
          , inn = inn
          , right_dec = goDec args right_dec
          , endd = endd
          }
    | Ast.Exp.DecOpen _ => dec
    | Ast.Exp.DecMultiple {elems, delims} =>
        Ast.Exp.DecMultiple
          {elems = Seq.map (goDec args) elems, delims = delims}
    | Ast.Exp.DecInfix _ => dec
    | Ast.Exp.DecInfixr _ => dec
    | Ast.Exp.DecNonfix _ => dec
  and goStrExp [] exp = exp
    | goStrExp args exp =
        (case exp of
           Ast.Str.Ident _ => exp
         | Ast.Str.Struct {structt, strdec, endd} =>
             Ast.Str.Struct
               {structt = structt, strdec = goStrDec args strdec, endd = endd}
         | Ast.Str.Constraint {strexp, colon, sigexp} =>
             Ast.Str.Constraint
               {strexp = goStrExp args strexp, colon = colon, sigexp = sigexp}
         | Ast.Str.FunAppExp {funid, lparen, strexp, rparen} =>
             Ast.Str.FunAppExp
               { funid = funid
               , lparen = lparen
               , strexp = goStrExp args strexp
               , rparen = rparen
               }
         | Ast.Str.FunAppDec {funid, lparen, strdec, rparen} =>
             Ast.Str.FunAppDec
               { funid = funid
               , lparen = lparen
               , strdec = goStrDec args strdec
               , rparen = rparen
               }
         | Ast.Str.LetInEnd {lett, strdec, inn, strexp, endd} =>
             Ast.Str.LetInEnd
               { lett = lett
               , strdec = goStrDec args strdec
               , inn = inn
               , strexp = goStrExp args strexp
               , endd = endd
               })
  and goStrDec args dec =
    case dec of
      Ast.Str.DecEmpty => dec
    | Ast.Str.DecCore dec => Ast.Str.DecCore (goDec args dec)
    | Ast.Str.DecStructure {structuree, elems, delims} =>
        let
          val elems =
            Seq.map
              (fn {strid, constraint, eq, strexp} =>
                 { strid = strid
                 , constraint = constraint
                 , eq = eq
                 , strexp =
                     goStrExp (filterToken (Token.toString strid) args) strexp
                 }) elems
        in
          Ast.Str.DecStructure
            {structuree = structuree, elems = elems, delims = delims}
        end
    | Ast.Str.DecMultiple {elems, delims} =>
        Ast.Str.DecMultiple
          {elems = Seq.map (goStrDec args) elems, delims = delims}
    | Ast.Str.DecLocalInEnd {locall, strdec1, inn, strdec2, endd} =>
        Ast.Str.DecLocalInEnd
          { locall = locall
          , strdec1 = goStrDec args strdec1
          , inn = inn
          , strdec2 = goStrDec args strdec2
          , endd = endd
          }
    | Ast.Str.MLtonOverload _ => dec
  and goFunDec args (Ast.Fun.DecFunctor {functorr, elems, delims}) =
    let
      val elems =
        Seq.map
          (fn {funid, lparen, funarg, rparen, constraint, eq, strexp} =>
             { funid = funid
             , lparen = lparen
             , funarg = funarg
             , rparen = rparen
             , constraint = constraint
             , eq = eq
             , strexp =
                 goStrExp (filterToken (Token.toString funid) args) strexp
             }) elems
    in
      Ast.Fun.DecFunctor {functorr = functorr, elems = elems, delims = delims}
    end
  and goTopDec args (dec: Ast.topdec) =
    case dec of
      Ast.SigDec _ => dec
    | Ast.StrDec dec => Ast.StrDec (goStrDec args dec)
    | Ast.FunDec dec => Ast.FunDec (goFunDec args dec)
    | Ast.TopExp {exp, semicolon} =>
        Ast.TopExp {exp = goExp args exp, semicolon = semicolon}
in
  fun gen args (Ast.Ast topdecs : Ast.t) =
    Ast.Ast
      (Seq.map
         (fn {topdec, semicolon} =>
            {topdec = goTopDec args topdec, semicolon = semicolon}) topdecs)
end

fun doSML (filepath, args) =
  let
    val fp = FilePath.fromUnixPath filepath
    val hfp = FilePath.toHostPath fp
    val source = Source.loadFromFile fp
    val allTokens = Lexer.tokens allows source
    val result = Parser.parse allows allTokens
  in
    case result of
      Parser.Ast ast =>
        let
          val ast = gen args ast
          val outstream = TextIO.openOut hfp
          val result =
            TerminalColorString.toString {colors = false} (pretty ast)
        in
          TextIO.output (outstream, result)
        end
    | _ => raise Fail "Just comments"
  end

fun parseArg (arg: string) : string list * gen =
  case String.tokens (fn ch => ch = #":") arg of
    typ :: opts :: [] =>
      ( String.tokens (fn ch => ch = #".") typ
      , CharVector.foldl (fn (ch, acc) => addGen acc (lookupGen ch)) emptyGen
          opts
      )
  | _ => raise Fail "bar"

val info =
  case CommandLineArgs.positional () of
    file :: args => (file, List.map parseArg args)
  | [] => raise Fail "Not enough arguments"

val () = doSML info
