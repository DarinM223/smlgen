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
PolyML.SaveState.loadState "save" handle _ => (
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-format-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/dynamic-array-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/dynamic-array.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-priorityq-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/priority-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/left-priorityq-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/ord-key-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/ord-map-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/lib-base-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/lib-base.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-redblack-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/uref-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/simple-uref.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-binary-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-xprod-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-xprod.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/path-util-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/bit-array-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/bit-array.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/ord-set-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/redblack-set-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-dynamic-array-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/bsearch-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/random-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/random.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/real-order-stats.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/io-util-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/io-util.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/fifo-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-key-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-hash-table-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-table-rep.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-hash-table.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-set-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/getopt-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/getopt.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-redblack-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/path-util.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-list-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-map-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/splaytree-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-array-sort-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/array-qsort-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-hash-set-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-set-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/graph-scc-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/redblack-map-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/graph-scc-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/base64-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/interval-domain-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/interval-set-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-hash2-table-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/format-comb-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/format-comb.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/fnv-hash.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/binary-map-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/fifo.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/parser-comb-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/parser-comb.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-binary-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-table-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/array-sort-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/array-qsort.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/format-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-table-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-table.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/char-map-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-redblack-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/queue-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/queue.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/word-redblack-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-table.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/int-list-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/splaytree.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/splay-set-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/base64.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/plist-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/plist.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/keyword-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/univariate-stats.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/binary-set-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-binary-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-binary-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/target64-prime-sizes.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-redblack-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/rand-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/char-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/mono-array-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/real-format.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/fmt-fields.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/format.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/scan-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/scan.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/atom-map.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/interval-set-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash2-table-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/splay-map-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/word-hash-table.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/utf8-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/utf8.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/rand.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/hash-string.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-format.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/dynamic-array-fn.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/word-redblack-set.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/listsort-sig.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/list-mergesort.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/uref.sml";
use "/usr/local/lib/mlton/sml/smlnj-lib/Util/ansi-term.sml";
use "smlfmt/src/base/Util.sml";
use "smlfmt/src/base/SeqBasis.sml";
use "smlfmt/src/base/ReadFile.sml";
use "smlfmt/src/base/BinarySearch.sml";
use "smlfmt/src/base/CommandLineArgs.sml";
use "smlfmt/src/base/Seq.sml";
use "smlfmt/src/base/ExnHistory.smlnj.sml";
use "smlfmt/src/base/SimplePromise.sml";
use "smlfmt/src/base/MemoizedPromise.sml";
use "smlfmt/src/base/TerminalColors.sml";
use "smlfmt/src/base/TextFormat.sml";
use "smlfmt/src/base/FilePath.sml";
use "smlfmt/src/base/FindInPath.sml";
use "smlfmt/src/base/RunProcess.smlnj.sml";
use "smlfmt/src/base/MLtonPathMap.sml";
use "smlfmt/src/base/Terminal.sml";
use "smlfmt/src/base/Source.sml";
use "smlfmt/src/base/WithSource.sml";
use "smlfmt/src/base/StripEffectiveWhitespace.sml";
use "smlfmt/src/base/Palette.sml";
use "smlfmt/src/base/TerminalColorString.sml";
use "smlfmt/src/base/Error.sml";
use "smlfmt/src/base/Dict.sml";
use "smlfmt/src/base/Set.sml";
use "smlfmt/src/base/DocVar.sml";
use "smlfmt/src/base/Tab.sml";
use "smlfmt/src/base/PrettySimpleDoc.sml";
use "smlfmt/src/base/PrettyTabbedDoc.sml";
use "smlfmt/src/base/AstAllows.sml";
use "smlfmt/src/lex/LexUtils.sml";
use "smlfmt/src/lex/Token.sml";
use "smlfmt/src/lex/Lexer.sml";
use "smlfmt/src/ast/MaybeLongToken.sml";
use "smlfmt/src/ast/AstType.sml";
use "smlfmt/src/ast/Ast.sml";
use "smlfmt/src/ast/CompareAst.sml";
use "smlfmt/src/parse/InfixDict.sml";
use "smlfmt/src/parse/ParserCombinators.sml";
use "smlfmt/src/parse/ParserUtils.sml";
use "smlfmt/src/parse/ExpPatRestriction.sml";
use "smlfmt/src/parse/FixExpPrecedence.sml";
use "smlfmt/src/parse/ParseSimple.sml";
use "smlfmt/src/parse/ParseTy.sml";
use "smlfmt/src/parse/ParsePat.sml";
use "smlfmt/src/parse/ParseFunNameArgs.sml";
use "smlfmt/src/parse/ParseExpAndDec.sml";
use "smlfmt/src/parse/ParseSigExpAndSpec.sml";
use "smlfmt/src/parse/Parser.sml";
use "smlfmt/src/syntax-highlighting/SyntaxHighlighter.sml";
use "smlfmt/src/prettier-print/TabbedTokenDoc.sml";
use "smlfmt/src/prettier-print/PrettierUtil.sml";
use "smlfmt/src/prettier-print/PrettierTy.sml";
use "smlfmt/src/prettier-print/PrettierPat.sml";
use "smlfmt/src/prettier-print/PrettierExpAndDec.sml";
use "smlfmt/src/prettier-print/PrettierSigUtil.sml";
use "smlfmt/src/prettier-print/PrettierSig.sml";
use "smlfmt/src/prettier-print/PrettierStrUtil.sml";
use "smlfmt/src/prettier-print/PrettierStr.sml";
use "smlfmt/src/prettier-print/PrettierFun.sml";
use "smlfmt/src/prettier-print/PrettierPrintAst.sml";
PolyML.SaveState.saveState "save" );
use "Fold.sml";
use "FunctionalRecordUpdate.sml";
use "BuildAst.sml";
use "Utils.sml";
use "MutRecTy.sig";
use "MutRecTy.sml";
use "FruGen.sml";
use "GenericGen.sml";
use "Env.sml";
use "ShowGen.sml";
use "CompareGen.sml";
use "FilesData.sml";
use "FilesGen.sml";
use "smlgen.sml";
