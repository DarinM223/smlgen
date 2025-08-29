structure Options =
struct
  val maxTySize = ref 100
  val defaultTableSize = ref 100
  val maxExpDepth = ref 100

  type opts =
    { test: bool
    , printOnly: bool
    , recursiveModules: bool
    , fileGen: string
    , projGen: string
    , maxSize: int
    , defaultTableSize: int
    , maxExpDepth: int
    , help: bool
    , interactive: bool
    }
  fun updateOpts r =
    let
      fun from test printOnly recursiveModules fileGen projGen maxSize
        defaultTableSize maxExpDepth help interactive =
        { test = test
        , printOnly = printOnly
        , recursiveModules = recursiveModules
        , fileGen = fileGen
        , projGen = projGen
        , maxSize = maxSize
        , defaultTableSize = defaultTableSize
        , maxExpDepth = maxExpDepth
        , help = help
        , interactive = interactive
        }
      fun to ?
        { test
        , printOnly
        , recursiveModules
        , fileGen
        , projGen
        , maxSize
        , defaultTableSize
        , maxExpDepth
        , help
        , interactive
        } =
        ?test printOnly recursiveModules fileGen projGen maxSize
          defaultTableSize maxExpDepth help interactive
    in
      FunctionalRecordUpdate.makeUpdate10 (from, from, to) r
    end
  val defaultOpts: opts =
    { test = false
    , printOnly = true
    , recursiveModules = false
    , fileGen = ""
    , projGen = ""
    , maxSize = !maxTySize
    , defaultTableSize = !defaultTableSize
    , maxExpDepth = !maxExpDepth
    , help = false
    , interactive = false
    }

  val opts = let open Fold FunctionalRecordUpdate
             in updateOpts defaultOpts set #recursiveModules true $
             end

  val search = fn key =>
    Option.isSome (List.find (fn a => a = key) (CommandLine.arguments ()))
  val parseFlag' = fn key => search ("-" ^ key)

  fun parseOpts () =
    { test = CommandLineArgs.parseFlag "test" orelse parseFlag' "t"
    , printOnly = CommandLineArgs.parseFlag "print" orelse parseFlag' "p"
    , recursiveModules =
        CommandLineArgs.parseFlag "recurmod" orelse parseFlag' "r"
    , fileGen = CommandLineArgs.parseString "gen" ""
    , projGen = CommandLineArgs.parseString "proj" ""
    , maxSize = CommandLineArgs.parseInt "maxsize" (!maxTySize)
    , defaultTableSize =
        CommandLineArgs.parseInt "tablesize" (!defaultTableSize)
    , maxExpDepth = CommandLineArgs.parseInt "maxexpdepth" (!maxExpDepth)
    , help = CommandLineArgs.parseFlag "help" orelse parseFlag' "h"
    , interactive =
        CommandLineArgs.parseFlag "interactive" orelse parseFlag' "i"
    }

  (* Similar to CommandLineArgs.positional () but handles shortened args like -p *)
  fun positional () =
    let
      fun loop found rest =
        case rest of
          [] => List.rev found
        | [x] =>
            List.rev (if not (String.isPrefix "-" x) then x :: found else found)
        | x :: y :: rest' =>
            if not (String.isPrefix "-" x) then
              loop (x :: found) (y :: rest')
            else if String.isPrefix "--" x then
              loop found (y :: rest')
            else if x = "-t" orelse x = "-p" orelse x = "-r" then
              loop found (y :: rest')
            else
              loop found rest'
    in
      loop [] (CommandLine.arguments ())
    end
end
