# Builds the PolyML's build.sml file from the smlgen.mlb file.
#
# The built file doesn't compile out of the box with PolyML,
# you have to change smlfmt/src/base/ExnHistory.mlton.sml to
# smlfmt/src/base/ExnHistory.smlnj.sml and
# smlfmt/src/base/RunProcess.mlton.sml to
# smlfmt/src/base/RunProcess.smlnj.sml.

cat > build.sml <<EOL
structure Unsafe =
struct
  structure Basis =
  struct
    structure Array = Array
    structure Vector = Vector
    structure CharArray = CharArray
    structure CharVector = CharVector
    structure Word8Array = Word8Array
    structure Word8Vector = Word8Vector
  end

  structure Vector = struct val sub = Basis.Vector.sub end

  structure Array =
  struct
    val sub = Basis.Array.sub
    val update = Basis.Array.update
    val create = Basis.Array.array
  end

  structure CharArray =
  struct
    open Basis.CharArray
    fun create i =
      array (i, chr 0)
  end

  structure CharVector =
  struct
    open Basis.CharVector
    fun create i =
      Basis.CharArray.vector (Basis.CharArray.array (i, chr 0))
    fun update (vec, i, el) =
      raise Fail "Unimplemented: Unsafe.CharVector.update"
  end

  structure Word8Array =
  struct
    open Basis.Word8Array
    fun create i = array (i, 0w0)
  end

  structure Word8Vector =
  struct
    open Basis.Word8Vector
    fun create i =
      Basis.Word8Array.vector (Basis.Word8Array.array (i, 0w0))
    fun update (vec, i, el) =
      raise Fail "Unimplemented: Unsafe.Word8Vector.update"
  end

  structure Real64Array =
  struct
    open Basis.Array
    type elem = Real.real
    type array = elem array
    fun create i = array (i, 0.0)
  end
end;
fun useProject root' file =
  let val root = OS.FileSys.getDir ()
  in
    OS.FileSys.chDir root';
    use file;
    OS.FileSys.chDir root
  end;
(* Uncomment this and put library files in here to prevent reloading them each time. *)
(*
PolyML.SaveState.loadState "save" handle _ => (
PolyML.SaveState.saveState "save" );
*)
EOL

mlton -stop f smlgen.mlb \
    | grep -v ".mlb" \
    | grep -v "/usr/local/lib/mlton/sml/basis/" \
    | grep -v "/usr/local/lib/mlton/targets/" \
    | grep -v "^main.sml" \
    | while read line ; do echo "use \"$line\";" ; done \
    >> build.sml
