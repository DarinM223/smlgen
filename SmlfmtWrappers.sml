structure HashUtils =
struct
  val combine = fn (a, b) => 0w31 * a + b
  fun hashList _ [] = 0wx6D52A54D
    | hashList hash l =
        List.foldl (fn (i, acc) => combine (acc, hash i))
          (Word.fromInt (List.length l)) l
  fun eqList eq (x :: xs, y :: ys) =
        eq (x, y) andalso eqList eq (xs, ys)
    | eqList _ ([], []) = true
    | eqList _ _ = false
  val hashString =
    #1
    o
    Substring.foldl
      (fn (ch, (h, p)) =>
         ( Word.mod (h + Word.fromInt (Char.ord ch + 1) * p, 0w1000000009)
         , Word.mod (p * 0w31, 0w1000000009)
         )) (0w0, 0w1) o Substring.full
end

structure Seq =
struct
  open Seq
  local open HashUtils
  in
    val hash = fn a_ => hashList a_ o Seq.toList
    val op== = fn a_ => fn (l1, l2) => eqList a_ (Seq.toList l1, Seq.toList l2)
  end
end

structure Token =
struct
  open Token
  val op== = Token.same
  local open HashUtils
  in val hash = hashString o Token.toString
  end
end

structure MaybeLongToken =
struct
  open MaybeLongToken
  val op== = fn (a, b) => Token.== (getToken a, getToken b)
  val hash = Token.hash o getToken
end

structure Ast =
struct
  open Ast
  structure SyntaxSeq =
  struct
    open SyntaxSeq
    local open HashUtils
    in
      val hash = fn a_ =>
        fn Empty => hashString "Empty"
         | One t0 => combine (hashString "One", a_ t0)
         | Many {left = t1, elems = t2, delims = t3, right = t4} =>
          let
            val result = hashString "Many"
            val result = combine (result, Token.hash t1)
            val result = combine (result, Seq.hash a_ t2)
            val result = combine (result, Seq.hash Token.hash t3)
            val result = combine (result, Token.hash t4)
          in
            result
          end
    end
    val op== = fn a_ =>
      fn (Empty, Empty) => true
       | (One t0, One t1) => a_ (t0, t1)
       | ( Many {left = t2, elems = t3, delims = t4, right = t5}
         , Many {left = t6, elems = t7, delims = t8, right = t9}
         ) =>
        Token.== (t2, t6) andalso Seq.== a_ (t3, t7)
        andalso Seq.== Token.== (t4, t8) andalso Token.== (t5, t9)
       | _ => false
  end

  structure Ty =
  struct
    open Ty
    local
      open HashUtils
      val rec ty = fn ty_0 =>
        fn Var t0 => combine (hashString "Var", Token.hash t0)
         | Record {left = t1, elems = t2, delims = t3, right = t4} =>
          let
            val result = hashString "Record"
            val result = combine (result, Token.hash t1)
            val result = combine
              ( result
              , Seq.hash
                  (fn {lab = t0, colon = t1, ty = t2} =>
                     let
                       val result = Token.hash t0
                       val result = combine (result, Token.hash t1)
                       val result = combine (result, ty_0 t2)
                     in
                       result
                     end) t2
              )
            val result = combine (result, Seq.hash Token.hash t3)
            val result = combine (result, Token.hash t4)
          in
            result
          end
         | Tuple {elems = t5, delims = t6} =>
          let
            val result = hashString "Tuple"
            val result = combine (result, Seq.hash ty_0 t5)
            val result = combine (result, Seq.hash Token.hash t6)
          in
            result
          end
         | Con {args = t7, id = t8} =>
          let
            val result = hashString "Con"
            val result = combine (result, SyntaxSeq.hash ty_0 t7)
            val result = combine (result, MaybeLongToken.hash t8)
          in
            result
          end
         | Arrow {from = t9, arrow = t10, to = t11} =>
          let
            val result = hashString "Arrow"
            val result = combine (result, ty_0 t9)
            val result = combine (result, Token.hash t10)
            val result = combine (result, ty_0 t11)
          in
            result
          end
         | Parens {left = t12, ty = t13, right = t14} =>
          let
            val result = hashString "Parens"
            val result = combine (result, Token.hash t12)
            val result = combine (result, ty_0 t13)
            val result = combine (result, Token.hash t14)
          in
            result
          end
      val ty = fn () => let val rec ty_0 = fn ? => ty ty_0 ? in ty_0 end
    in val hash = ty ()
    end
    local
      val rec ty = fn ty_0 =>
        fn (Var t0, Var t1) => Token.== (t0, t1)
         | ( Record {left = t2, elems = t3, delims = t4, right = t5}
           , Record {left = t6, elems = t7, delims = t8, right = t9}
           ) =>
          Token.== (t2, t6)
          andalso
          Seq.==
            (fn ( {lab = t0, colon = t1, ty = t2}
                , {lab = t3, colon = t4, ty = t5}
                ) =>
               Token.== (t0, t3) andalso Token.== (t1, t4) andalso ty_0 (t2, t5))
            (t3, t7) andalso Seq.== Token.== (t4, t8) andalso Token.== (t5, t9)
         | ( Tuple {elems = t10, delims = t11}
           , Tuple {elems = t12, delims = t13}
           ) => Seq.== ty_0 (t10, t12) andalso Seq.== Token.== (t11, t13)
         | (Con {args = t14, id = t15}, Con {args = t16, id = t17}) =>
          SyntaxSeq.== ty_0 (t14, t16) andalso MaybeLongToken.== (t15, t17)
         | ( Arrow {from = t18, arrow = t19, to = t20}
           , Arrow {from = t21, arrow = t22, to = t23}
           ) =>
          ty_0 (t18, t21) andalso Token.== (t19, t22) andalso ty_0 (t20, t23)
         | ( Parens {left = t24, ty = t25, right = t26}
           , Parens {left = t27, ty = t28, right = t29}
           ) =>
          Token.== (t24, t27) andalso ty_0 (t25, t28)
          andalso Token.== (t26, t29)
         | _ => false
      val ty = fn () => let val rec ty_0 = fn ? => ty ty_0 ? in ty_0 end
    in val op== = ty ()
    end
  end
end
