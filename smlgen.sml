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

  fun lookupGen #"g" = GenericGen.gen
    | lookupGen #"u" = FruGen.gen
    | lookupGen #"s" = ShowGen.gen
    | lookupGen #"c" = CompareGen.gen
    | lookupGen ch =
        raise Fail ("unknown lookup character: " ^ Char.toString ch)

  fun printToken t =
    ( print (Token.toString t ^ ":")
    ; print
        (Int.toString (#line (Source.absoluteEnd (Token.getSource t))) ^ " ")
    )
  fun printDecTypes (Ast.Exp.DecType {typbind = {elems, ...}, ...}) =
        ArraySlice.app (fn e => printToken (#tycon e)) elems
    | printDecTypes (Ast.Exp.DecDatatype {datbind = {elems, ...}, ...}) =
        ArraySlice.app (fn e => printToken (#tycon e)) elems
    | printDecTypes (Ast.Exp.DecReplicateDatatype {left_id, ...}) =
        printToken left_id
    | printDecTypes _ = raise Fail "Unknown declaration type"

  fun datbindActions args : Ast.Exp.datbind -> Utils.gen option =
    Option.join
    o Option.map (fn e => getActions (Token.toString (#tycon e)) args)
    o
    ArraySlice.find (fn e =>
      Option.isSome (getActions (Token.toString (#tycon e)) args)) o #elems
  fun typbindActions args : Ast.Exp.typbind -> Utils.gen option =
    Option.join
    o Option.map (fn e => getActions (Token.toString (#tycon e)) args)
    o
    ArraySlice.find (fn e =>
      Option.isSome (getActions (Token.toString (#tycon e)) args)) o #elems

  fun parseArg (arg: string) : string list * Utils.gen =
    case String.tokens (fn ch => ch = #":") arg of
      typ :: opts :: [] =>
        ( String.tokens (fn ch => ch = #".") typ
        , CharVector.foldl (fn (ch, acc) => Utils.addGen acc (lookupGen ch))
            Utils.emptyGen opts
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


  fun confirm (opts: Options.opts) dec next =
    if #test opts orelse #recursiveModules opts then
      Utils.combineDecs dec (next ())
    else if #printOnly opts then
      ( print "\n"
      ; print (TerminalColorString.toString {colors = true}
          (Utils.prettyDec (next ())))
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
              if line = "Y\n" then Utils.combineDecs dec (next ())
              else if line = "N\n" then dec
              else confirm opts dec next
            end
      )

  fun goDecType (opts: Options.opts) (args, dec, typbind) =
    case typbindActions args typbind of
      SOME action =>
        ( print "Types: "
        ; printDecTypes dec
        ; confirm opts dec (fn () => #genTypebind action typbind)
        )
    | NONE => dec

  type args = (string list * Utils.gen) list

  fun visitor (opts: Options.opts) (args: args) : args AstVisitor.visitor =
    { state = args
    , goDecType = goDecType opts
    , goDecReplicateDatatype = fn (args, dec, left, right) =>
        let val typbind = BuildAst.replicateDatatypeToTypbind left right
        in goDecType opts (args, dec, typbind)
        end
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
                ; confirm opts dec (fn () =>
                    #genDatabind action datbind (Option.map #typbind withtypee))
                )
            | NONE => dec
          end
    , onStructure = fn strid => filterToken (Token.toString strid)
    , onFunctor = fn funid => filterToken (Token.toString funid)
    }

  fun gen (opts: Options.opts) (args: args) (Ast.Ast topdecs : Ast.t) =
    Ast.Ast
      (Seq.map
         (fn {topdec, semicolon} =>
            { topdec = AstVisitor.goTopDec (visitor opts args) topdec
            , semicolon = semicolon
            }) topdecs)

  fun doSML (opts: Options.opts) (filepath: string, args: string list) =
    let
      val args: args = List.map parseArg args
      val fp = FilePath.fromUnixPath filepath
      val hfp = FilePath.toHostPath
        (if #test opts then
           FilePath.fromUnixPath (filepath ^ ".test")
         else if #recursiveModules opts then
           Utils.mapBasename (Utils.mapBase (fn base => base ^ ".rec")) fp
         else
           fp)
      val source = Source.loadFromFile fp
      val allTokens = Lexer.tokens allows source
      val result = Parser.parse allows allTokens
    in
      case result of
        Parser.Ast ast =>
          let
            val (ast, substTable) =
              if #recursiveModules opts then RecMod.gen ast
              else (ast, RecMod.emptySubstTable ())
            val args = RecMod.substArgs substTable args
            val ast = gen opts args ast
            val prettyAst = fn colors =>
              TerminalColorString.toString {colors = colors} (Utils.pretty ast)
          in
            if #printOnly opts then
              if #recursiveModules opts then
                (print (prettyAst true); print "\n")
              else
                ()
            else
              TextIO.output (TextIO.openOut hfp, prettyAst false)
          end
      | _ => raise Fail "Just comments"
    end


  fun main _ =
    let
      val opts as {maxSize, defaultTableSize, fileGen, projGen, ...} =
        { test = CommandLineArgs.parseFlag "test"
        , printOnly = CommandLineArgs.parseFlag "print"
        , recursiveModules = CommandLineArgs.parseFlag "recurmod"
        , fileGen = CommandLineArgs.parseString "gen" ""
        , projGen = CommandLineArgs.parseString "proj" ""
        , maxSize = CommandLineArgs.parseInt "maxsize" (! Options.maxTySize)
        , defaultTableSize =
            CommandLineArgs.parseInt "tablesize" (! Options.defaultTableSize)
        }

      val () =
        if maxSize <> ! Options.maxTySize then
          ( print ("Setting max type size to: " ^ Int.toString maxSize ^ "\n")
          ; Options.maxTySize := maxSize
          )
        else
          ()

      val () =
        if defaultTableSize <> ! Options.defaultTableSize then
          ( print
              ("Setting default table size to: " ^ Int.toString defaultTableSize
               ^ "\n")
          ; Options.defaultTableSize := defaultTableSize
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
          List.app (fn file :: args => doSML opts (file, args) | _ => ())
            (collectSMLFiles [] args);
      OS.Process.success
    end
end

val main = fn () => ignore (Main.main ("", []))
