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

  fun main _ =
    let
      val test = CommandLineArgs.parseFlag "test"
      val printOnly = CommandLineArgs.parseFlag "print"
      val recursiveModules = CommandLineArgs.parseFlag "recurmod"
      val fileGen = CommandLineArgs.parseString "gen" ""
      val projGen = CommandLineArgs.parseString "proj" ""
      val maxSize = CommandLineArgs.parseInt "maxsize" (! MutRecTy.maxTySize)

      fun confirm dec next =
        if test orelse recursiveModules then
          Utils.combineDecs dec (next ())
        else if printOnly then
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
        , onFunctor = fn funid => filterToken (Token.toString funid)
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
            (if test then
               FilePath.fromUnixPath (filepath ^ ".test")
             else if recursiveModules then
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
                  if recursiveModules then RecMod.gen ast
                  else (ast, RecMod.emptySubstTable ())
                val args = RecMod.substArgs substTable args
                val ast = gen args ast
                val prettyAst = fn colors =>
                  TerminalColorString.toString {colors = colors}
                    (Utils.pretty ast)
              in
                if printOnly then
                  if recursiveModules then (print (prettyAst true); print "\n")
                  else ()
                else
                  TextIO.output (TextIO.openOut hfp, prettyAst false)
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
