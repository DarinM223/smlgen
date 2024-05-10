structure Options =
struct
  val maxTySize = ref 100
  val defaultTableSize = ref 100

  type opts =
    { test: bool
    , printOnly: bool
    , recursiveModules: bool
    , fileGen: string
    , projGen: string
    , maxSize: int
    , defaultTableSize: int
    }
  fun updateOpts r =
    let
      fun from test printOnly recursiveModules fileGen projGen maxSize
        defaultTableSize =
        { test = test
        , printOnly = printOnly
        , recursiveModules = recursiveModules
        , fileGen = fileGen
        , projGen = projGen
        , maxSize = maxSize
        , defaultTableSize = defaultTableSize
        }
      fun to ?
        { test
        , printOnly
        , recursiveModules
        , fileGen
        , projGen
        , maxSize
        , defaultTableSize
        } =
        ?test printOnly recursiveModules fileGen projGen maxSize
          defaultTableSize
    in
      FunctionalRecordUpdate.makeUpdate7 (from, from, to) r
    end
  val defaultOpts: opts =
    { test = false
    , printOnly = true
    , recursiveModules = false
    , fileGen = ""
    , projGen = ""
    , maxSize = !maxTySize
    , defaultTableSize = !defaultTableSize
    }

  val opts = let open Fold FunctionalRecordUpdate
             in updateOpts defaultOpts set #recursiveModules true $
             end
end
