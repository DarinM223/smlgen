structure Main =
struct
  fun filterToken tokenString ((token' :: path, actions) :: xs) =
        if token' = tokenString then
          (path, actions) :: filterToken tokenString xs
        else
          filterToken tokenString xs
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
  val prettyDec =
    pretty
    o (fn topdec => Ast.Ast (Seq.singleton {topdec = topdec, semicolon = NONE}))
    o Ast.StrDec o Ast.Str.DecCore

  type gen =
    { genTypebind: Ast.Exp.typbind -> Ast.Exp.dec
    , genDatabind: Ast.Exp.datbind -> Ast.Exp.typbind option -> Ast.Exp.dec
    }
  val emptyGen: gen =
    { genTypebind = fn _ => Ast.Exp.DecEmpty
    , genDatabind = fn _ => fn _ => Ast.Exp.DecEmpty
    }
  fun lookupGen #"g" = GenericGen.gen
    | lookupGen #"u" = FruGen.gen
    | lookupGen #"s" = ShowGen.gen
    | lookupGen #"c" = CompareGen.gen
    | lookupGen ch =
        raise Fail ("unknown lookup character: " ^ Char.toString ch)

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

  fun addGen (gen1: gen) (gen2: gen) : gen =
    { genTypebind = fn bind =>
        combineDecs (#genTypebind gen1 bind) (#genTypebind gen2 bind)
    , genDatabind = fn databind =>
        fn typebind =>
          combineDecs (#genDatabind gen1 databind typebind)
            (#genDatabind gen2 databind typebind)
    }

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

  fun datbindActions args : Ast.Exp.datbind -> gen option =
    Option.join
    o Option.map (fn e => getActions (Token.toString (#tycon e)) args)
    o
    ArraySlice.find (fn e =>
      Option.isSome (getActions (Token.toString (#tycon e)) args)) o #elems
  fun typbindActions args : Ast.Exp.typbind -> gen option =
    Option.join
    o Option.map (fn e => getActions (Token.toString (#tycon e)) args)
    o
    ArraySlice.find (fn e =>
      Option.isSome (getActions (Token.toString (#tycon e)) args)) o #elems

  fun parseArg (arg: string) : string list * gen =
    case String.tokens (fn ch => ch = #":") arg of
      typ :: opts :: [] =>
        ( String.tokens (fn ch => ch = #".") typ
        , CharVector.foldl (fn (ch, acc) => addGen acc (lookupGen ch)) emptyGen
            opts
        )
    | _ =>
        raise Fail "Invalid generator syntax: should be format type:generators"

  val isFile = fn file => not (Char.contains file #":")
  fun collectSMLFiles (top :: build) (file :: args) =
        if isFile file then collectSMLFiles ([file] :: top :: build) args
        else collectSMLFiles ((file :: top) :: build) args
    | collectSMLFiles [] (file :: args) =
        if isFile file then collectSMLFiles [[file]] args
        else collectSMLFiles [] args
    | collectSMLFiles build [] =
        List.map List.rev (List.rev build)

  fun main _ =
    let
      val test = CommandLineArgs.parseFlag "test"
      val printOnly = CommandLineArgs.parseFlag "print"
      val recursiveModules = CommandLineArgs.parseFlag "recurmod"
      val fileGen = CommandLineArgs.parseString "gen" ""
      val projGen = CommandLineArgs.parseString "proj" ""
      val maxSize = CommandLineArgs.parseInt "maxsize" (! MutRecTy.maxTySize)

      fun confirm dec next =
        if test then
          combineDecs dec (next ())
        else if printOnly then
          ( print "\n"
          ; print (TerminalColorString.toString {colors = true}
              (prettyDec (next ())))
          ; print "\n"
          ; dec
          )
        else
          ( print "\nConfirm [y/n]? "
          ; case TextIO.inputLine TextIO.stdIn of
              NONE => dec
            | SOME line =>
                let
                  val line = String.map Char.toUpper line
                in
                  if line = "Y\n" then combineDecs dec (next ())
                  else if line = "N\n" then dec
                  else confirm dec next
                end
          )
      fun visitor args =
        { state = args
        , goDecType = fn (args, dec, typbind) =>
            (case typbindActions args typbind of
               SOME action =>
                 ( print "Types: "
                 ; printDecTypes dec
                 ; confirm dec (fn () => #genTypebind action typbind)
                 )
             | NONE => dec)
        , goDecDatatype =
            fn (args, dec, datbind, withtypee: AstVisitor.withtypee) =>
              let
                val actions1 = datbindActions args datbind
                val actions2 = Option.join
                  (Option.map (typbindActions args o #typbind) withtypee)
                val actions =
                  case actions1 of
                    SOME action => SOME action
                  | NONE => actions2
              in
                case actions of
                  SOME action =>
                    ( print "Types: "
                    ; printDecTypes dec
                    ; confirm dec (fn () =>
                        #genDatabind action datbind
                          (Option.map #typbind withtypee))
                    )
                | NONE => dec
              end
        , onStructure = fn strid => filterToken (Token.toString strid)
        , onFunctor = fn strid => filterToken (Token.toString strid)
        }
      fun gen args (Ast.Ast topdecs : Ast.t) =
        Ast.Ast
          (Seq.map
             (fn {topdec, semicolon} =>
                { topdec = AstVisitor.goTopDec (visitor args) topdec
                , semicolon = semicolon
                }) topdecs)

      fun doSML (filepath, args) =
        let
          val fp = FilePath.fromUnixPath filepath
          val hfp = FilePath.toHostPath
            (if test then FilePath.fromUnixPath (filepath ^ ".test") else fp)
          val source = Source.loadFromFile fp
          val allTokens = Lexer.tokens allows source
          val result = Parser.parse allows allTokens
        in
          case result of
            Parser.Ast ast =>
              let
                val ast = if recursiveModules then RecMod.gen ast else ast
                val ast = gen args ast
                val result =
                  TerminalColorString.toString {colors = false} (pretty ast)
              in
                if printOnly then ()
                else TextIO.output (TextIO.openOut hfp, result)
              end
          | _ => raise Fail "Just comments"
        end

      val () =
        if maxSize <> ! MutRecTy.maxTySize then
          ( print ("Setting max type size to: " ^ Int.toString maxSize ^ "\n")
          ; MutRecTy.maxTySize := maxSize
          )
        else
          ()

      val () =
        case fileGen of
          "fru" => (print "Generating FRU\n"; FilesGen.genFiles FruFile.t)
        | "fold" => (print "Generating Fold\n"; FilesGen.genFiles FoldFile.t)
        | "fold01n" =>
            (print "Generating Fold01N\n"; FilesGen.genFiles Fold01NFile.t)
        | "product" =>
            (print "Generating product\n"; FilesGen.genFiles ProductFile.t)
        | "printf" =>
            (print "Generating printf\n"; FilesGen.genFiles PrintfFile.t)
        | "num" =>
            (print "Generating numeric literal\n"; FilesGen.genFiles NumFile.t)
        | "literal" =>
            ( print "Generating array literal\n"
            ; FilesGen.genFiles LiteralFile.t
            )
        | "optarg" =>
            ( print "Generating optional argument\n"
            ; FilesGen.genFiles OptionalArgFile.t
            )
        | _ => ()
      val () =
        if String.size projGen > 0 then FilesGen.genProject projGen else ()
    in
      case CommandLineArgs.positional () of
        [] => ()
      | args =>
          List.app
            (fn file :: args => doSML (file, List.map parseArg args) | _ => ())
            (collectSMLFiles [] args);
      OS.Process.success
    end
end

val main = fn () => ignore (Main.main ("", []))
