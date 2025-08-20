structure TabbedTokenDoc_TCS = TerminalColorString

structure TabbedTokenDoc_CustomString =
struct
  open TerminalColorString

  val compaction = CommandLineArgs.parseReal "s-compact" 1.1 (* must be >= 1 *)
  val maxSat = CommandLineArgs.parseReal "s-max" 0.6

  val hues = Seq.fromList [0, 30, 55, 90, 140, 180, 210, 250, 290, 320]

  fun niceRed depth =
    let
      val s =
        (compaction - 1.0 + (1.0 / (1.0 + (Real.fromInt depth / compaction))))
        / compaction
      val s = s * maxSat

      (* val d = if depth mod 2 = 0 then 2*(depth div 2)+1 else 2*(depth div 2) *)
      val d = 3 * (depth - 1)
      val h = Real.fromInt (Seq.nth hues (d mod Seq.length hues))
    in
      TerminalColors.hsv {h = h, s = s, v = 0.9}
    end

  fun emphasize depth s =
    backgroundIfNone (niceRed depth) s

  fun toString t =
    TerminalColorString.toString {colors = false} t
end


structure TabbedTokenDoc_Token =
struct
  open Token

  fun prevTokenNotWhitespace t =
    case Token.prevToken t of
      NONE => NONE
    | SOME p =>
        if Token.isWhitespace p then prevTokenNotWhitespace p else SOME p

  fun desiredBlankLinesBefore tok =
    case prevTokenNotWhitespace tok of
      NONE => 0
    | SOME prevTok =>
        let
          val diff = Token.lineDifference (prevTok, tok) - 1
          val diff = Int.max (0, Int.min (2, diff))
        in
          diff
        end

  val allCommentsBefore = Token.commentsBefore
  val allCommentsAfter = Token.commentsAfter

  (* Find index i where the first i comments should belong to tok, and the
   * rest belong to the next token. (tok, comments) must be adjacent.
   *)
  fun findSplit (tok, comments) =
    let
      val n = Seq.length comments
      fun loop i =
        if i >= n then n
        else if Token.lineDifference (tok, Seq.nth comments i) > 0 then i
        else loop (i + 1)
    in
      loop 0
    end

  fun splitCommentsBefore tok =
    case Token.prevTokenNotCommentOrWhitespace tok of
      NONE => allCommentsBefore tok
    | SOME ptok =>
        let
          val cs = allCommentsBefore tok
          val cs = Seq.drop cs (findSplit (ptok, cs))
        in
          cs
        end

  fun splitCommentsAfterAndBeforeNext tok =
    let
      val cs = allCommentsAfter tok
      val i = findSplit (tok, cs)
      val cs1 = Seq.take cs i
      val cs2 = Seq.drop cs i
    in
      (cs1, cs2)
    end

  fun splitCommentsAfter tok =
    let val (cs, _) = splitCommentsAfterAndBeforeNext tok
    in cs
    end
end

structure TabbedTokenDoc_Utils =
struct
  datatype pieces =
    OnePiece of TabbedTokenDoc_CustomString.t
  | ManyPieces of TabbedTokenDoc_CustomString.t Seq.t

  fun tokenToPieces {tabWidth: int} tok =
    if not (Token.isComment tok orelse Token.isStringConstant tok) then
      OnePiece (SyntaxHighlighter.highlightToken tok)
    else
      let
        val src = Token.getSource tok

        val effectiveOffset = Token.effectiveOffset {tabWidth = tabWidth} tok

        fun strip line =
          let
            val (_, ln) =
              TabbedTokenDoc_TCS.stripEffectiveWhitespace
                {tabWidth = tabWidth, removeAtMost = effectiveOffset} line
          in
            ln
          end

        val t = SyntaxHighlighter.highlightToken tok

        val pieces =
          Seq.map
            (fn (i, j) => strip (TabbedTokenDoc_TCS.substring (t, i, j - i)))
            (Source.lineRanges src)

        val numPieces = Seq.length pieces
      in
        if numPieces = 1 then OnePiece t else ManyPieces pieces
      end
end

structure TabbedTokenDoc =
  PrettyTabbedDoc
    (structure CustomString = TabbedTokenDoc_CustomString
     structure Token = TabbedTokenDoc_Token
     open TabbedTokenDoc_Utils)
