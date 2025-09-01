structure MainHelpers =
struct
  val noFilesDesc =
    "No files specified. Try running with --help or -h for more information.\n"
  val genDesc =
    "     u                  Functional record update\n\
    \     g                  Generic (type indexed values)\n\
    \     s                  Show\n\
    \     c                  Compare\n\
    \     e                  Equality\n\
    \     h                  Hash\n"
  val helpDesc =
    "Generate for types usage: [filename] [type]:[generator...]... [options]\n\
    \  type: Fully qualified type name (Example: Ast.Ty.ty)\n\
    \  generator:\n" ^ genDesc
    ^
    "  options:\n\
    \    --interactive, -i   Input datatypes through standard input\n\
    \    --print, -p         Print generated code to stdout instead of overwriting\n\
    \    --recurmod, -r      Break the recursive modules in the file\n\
    \    --test, -t          Create file with .test extension instead of overwriting\n\
    \    -maxsize <size>     The max type size limit for polymorphic recursion\n\
    \                        Default is 100\n\
    \    -tablesize <size>   The default size of hashtables used in smlgen\n\
    \                        Default is 100\n\
    \    -maxexpdepth <size> The max depth to look into expressions for types\n\
    \                        Default is 100, and negative means no limit\n\
    \\n\
    \Generate specific files usage: -gen <filetype>\n\
    \  filetype:\n\
    \     fru                Functional record update\n\
    \     fold               Fold\n\
    \     fold01n            Fold01N\n\
    \     product            Product type\n\
    \     printf             Printf\n\
    \     num                Numeric literals\n\
    \     literal            Array & Vector literals\n\
    \     optarg             Optional arguments\n\
    \\n\
    \Generate new project usage: -proj [dirname]\n\n"

  fun filterToken tokenString ((action as (["*"], _)) :: xs) =
        action :: filterToken tokenString xs
    | filterToken tokenString ((token' :: path, actions) :: xs) =
        if token' = tokenString then
          (path, actions) :: filterToken tokenString xs
        else
          filterToken tokenString xs
    | filterToken tokenString (_ :: xs) = filterToken tokenString xs
    | filterToken _ [] = []

  fun getActions _ ((["*"], actions) :: _) = SOME actions
    | getActions tokenString (([token'], actions) :: xs) =
        if token' = tokenString then SOME actions else getActions tokenString xs
    | getActions tokenString (_ :: xs) = getActions tokenString xs
    | getActions _ [] = NONE

  val allows = AstAllows.make
    { topExp = true
    , optBar = true
    , recordPun = true
    , orPat = true
    , extendedText = true
    , sigWithtype = true
    }

  fun lookupGen #"g" = GenericGen.gen
    | lookupGen #"u" = FruGen.gen
    | lookupGen #"s" = ShowGen.gen
    | lookupGen #"c" = CompareGen.gen
    | lookupGen #"e" = EqGen.gen
    | lookupGen #"h" = HashGen.gen
    | lookupGen ch =
        raise Fail ("unknown lookup character: " ^ Char.toString ch)

  fun printToken path t =
    let
      val t' = String.concatWith "." (List.rev (Token.toString t :: path))
    in
      print (t' ^ ":");
      print
        (Int.toString (#line (Source.absoluteEnd (Token.getSource t))) ^ " ")
    end
  fun printDecTypes path (Ast.Exp.DecType {typbind = {elems, ...}, ...}) =
        ArraySlice.app (fn e => printToken path (#tycon e)) elems
    | printDecTypes path (Ast.Exp.DecDatatype {datbind = {elems, ...}, ...}) =
        ArraySlice.app (fn e => printToken path (#tycon e)) elems
    | printDecTypes path (Ast.Exp.DecReplicateDatatype {left_id, ...}) =
        printToken path left_id
    | printDecTypes _ _ = raise Fail "Unknown declaration type"

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

  fun goDecType (opts: Options.opts) ((args, path), dec, typbind) =
    case typbindActions args typbind of
      SOME action =>
        ( print "Types: "
        ; printDecTypes path dec
        ; confirm opts dec (fn () => #genTypebind action typbind)
        )
    | NONE => dec

  type args = (string list * Utils.gen) list

  fun visitor (opts: Options.opts) (args: args) :
    (args * string list) AstVisitor.visitor =
    { state = (args, [])
    , goDecType = goDecType opts
    , goDecReplicateDatatype = fn (state, dec, left, right) =>
        let val typbind = BuildAst.replicateDatatypeToTypbind left right
        in goDecType opts (state, dec, typbind)
        end
    , goDecDatatype =
        fn ((args, path), dec, datbind, withtypee: AstVisitor.withtypee) =>
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
                ; printDecTypes path dec
                ; confirm opts dec (fn () =>
                    #genDatabind action datbind (Option.map #typbind withtypee))
                )
            | NONE => dec
          end
    , onStructure = fn strid =>
        fn (args, path) => let val strid = Token.toString strid
                           in (filterToken strid args, strid :: path)
                           end
    , onFunctor = fn funid =>
        fn (args, path) => let val funid = Token.toString funid
                           in (filterToken funid args, funid :: path)
                           end
    }

  fun gen (opts: Options.opts) (args: args) (Ast.Ast topdecs : Ast.t) =
    Ast.Ast
      (Seq.map
         (fn {topdec, semicolon} =>
            { topdec = AstVisitor.goTopDec (visitor opts args) topdec
            , semicolon = semicolon
            }) topdecs)

  fun printParseErrors e =
    TerminalColorString.print
      (Error.show {highlighter = SOME SyntaxHighlighter.fuzzyHighlight} e)

  fun clearScreen () =
    let val strm = TextIO.openOut (Posix.ProcEnv.ctermid ())
    in TextIO.output (strm, "\^[[H\^[[2J"); TextIO.closeOut strm
    end

  fun doSML (opts: Options.opts) (filepath: string, args: string list) =
    let
      val () = print ("Generating code for file: " ^ filepath ^ "\n")
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
              let
                val out = TextIO.openOut hfp
              in
                TextIO.output (out, prettyAst false);
                TextIO.flushOut out;
                TextIO.closeOut out
              end
          end
      | _ => print "Just comments... Skipping\n"
    end
    handle Error.Error e => printParseErrors e

  fun doInteractive (opts: Options.opts) =
    let
      val opts = let open Fold FunctionalRecordUpdate
                 in Options.updateOpts opts set #printOnly true $
                 end
      fun parse source k =
        let
          val parsed = let val allTokens = Lexer.tokens allows source
                       in SOME (Parser.parse allows allTokens)
                       end
                       handle Error.Error e => (printParseErrors e; NONE)
        in
          case parsed of
            SOME parsed => k parsed
          | NONE => go ()
        end
      and inputGenerators k =
        ( print "Generators ('help' for help): "
        ; case TextIO.inputLine TextIO.stdIn of
            SOME line =>
              if FilesGen.trim line = "help" then
                ( print
                    "Enter a string with each character corresponding to a generator:\n"
                ; print genDesc
                ; inputGenerators k
                )
              else
                let
                  val filtered = (String.implode
                    (List.filter
                       (fn ch => (lookupGen ch; true) handle _ => false)
                       (String.explode line)))
                in
                  if filtered = "" then
                    ( print "Invalid generators, retrying...\n"
                    ; inputGenerators k
                    )
                  else
                    k filtered
                end
          | NONE => go ()
        )
      and go () =
        let
          val () = print "Enter Standard ML code (Ctrl-D for end of input):\n"
          val source = Source.loadFromStdin ()
        in
          parse source
            (fn Parser.Ast (ast as Ast.Ast topdecs) =>
               if ArraySlice.isEmpty topdecs then
                 (clearScreen (); go ())
               else
                 inputGenerators (fn line =>
                   let
                     val args = ["*:" ^ line]
                     val args: args = List.map parseArg args
                     val _ = gen opts args ast
                   in
                     print "\n";
                     go ()
                   end)
              | _ =>
               (clearScreen (); print "Just comments... Skipping\n"; go ()))
        end
    in
      go ()
    end

end

structure Main =
struct
  fun main _ =
    let
      val opts as {maxSize, projGen, ...} = Options.parseOpts ()

      val () = if #help opts then print MainHelpers.helpDesc else ()

      val () =
        if maxSize <> ! Options.maxTySize then
          ( print ("Setting max type size to: " ^ Int.toString maxSize ^ "\n")
          ; Options.maxTySize := maxSize
          )
        else
          ()

      val () =
        if #defaultTableSize opts <> ! Options.defaultTableSize then
          ( print
              ("Setting default table size to: "
               ^ Int.toString (#defaultTableSize opts) ^ "\n")
          ; Options.defaultTableSize := #defaultTableSize opts
          )
        else
          ()

      val () =
        if #maxExpDepth opts <> ! Options.maxExpDepth then
          ( print
              ("Setting max expression depth to: "
               ^ Int.toString (#maxExpDepth opts) ^ "\n")
          ; Options.maxExpDepth := #maxExpDepth opts
          )
        else
          ()

      val () =
        case #fileGen opts of
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
      val args = Options.positional ()
      val files = MainHelpers.collectSMLFiles [] args
    in
      case files of
        [] => if not (#help opts) then print MainHelpers.noFilesDesc else ()
      | _ =>
          List.app
            (fn file :: args => MainHelpers.doSML opts (file, args) | _ => ())
            files;
      if #interactive opts then MainHelpers.doInteractive opts else ();
      OS.Process.success
    end
end

structure SmldotnetMain = struct val main = fn () => ignore (Main.main ()) end
