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
end
