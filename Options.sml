structure Options =
struct
  val maxTySize = ref 100

  type opts =
    { test: bool
    , printOnly: bool
    , recursiveModules: bool
    , fileGen: string
    , projGen: string
    , maxSize: int
    }
  val defaultOpts: opts =
    { test = false
    , printOnly = true
    , recursiveModules = false
    , fileGen = ""
    , projGen = ""
    , maxSize = !maxTySize
    }
  fun updateOpts r =
    let
      fun from test printOnly recursiveModules fileGen projGen maxSize =
        { test = test
        , printOnly = printOnly
        , recursiveModules = recursiveModules
        , fileGen = fileGen
        , projGen = projGen
        , maxSize = maxSize
        }
      fun to ? {test, printOnly, recursiveModules, fileGen, projGen, maxSize} =
        ?test printOnly recursiveModules fileGen projGen maxSize
    in
      FunctionalRecordUpdate.makeUpdate6 (from, from, to) r
    end

  val opts = let open Fold FunctionalRecordUpdate
             in updateOpts defaultOpts set #recursiveModules true $
             end
end
