structure FilesGen =
struct
  fun isWhitespace ch = ch = #" " orelse ch = #"\n"
  val trim =
    Substring.string o Substring.dropr isWhitespace
    o Substring.dropl isWhitespace o Substring.full

  exception Skip

  fun genFiles (FilesData.Data file) =
    let
      val () = List.app genFiles (#depends file)
      fun checkFileName (fileName: string) : string =
        if OS.FileSys.access (fileName, []) then
          ( print
              (fileName
               ^
               " already exists. Enter a new filename (or press enter to skip): \n")
          ; case Option.map trim (TextIO.inputLine TextIO.stdIn) of
              NONE => raise Skip
            | SOME "" => raise Skip
            | SOME fileName => checkFileName fileName
          )
        else
          fileName
      val fileName = checkFileName (#fileName file)
      val os = TextIO.openOut fileName
    in
      TextIO.output (os, #data file);
      TextIO.closeOut os
    end
    handle Skip => ()

  fun genProjectFiles projectName =
    let
      fun replaceCaret s =
        let
          val (l, r) = Substring.splitl (fn ch => ch <> #"^") (Substring.full s)
        in
          Substring.concat [l, Substring.full projectName, Substring.triml 1 r]
        end
      val cmFile = FilesData.mapFileName (fn s => projectName ^ s) CMFile.t
      val mlbFile = FilesData.mapFileName (fn s => projectName ^ s) MLBFile.t
      val milletFile = FilesData.mapData replaceCaret MilletFile.t
      val buildPolyFile = FilesData.mapData replaceCaret BuildPolyMLFile.t
    in
      List.app genFiles [cmFile, mlbFile, milletFile, buildPolyFile]
    end

  fun genProject projectName =
    ( OS.FileSys.mkDir projectName
    ; OS.FileSys.chDir projectName
    ; genProjectFiles projectName
    )
end
