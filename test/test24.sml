structure Foo =
struct
  type t =
    { a: string
    , b: int
    , c: real
    , d: char
    , e: word
    , f: String.string
    , g: String.char
    , h: Int.int
    , i: Int32.int
    , j: Int64.int
    , k: LargeInt.int
    , l: FixedInt.int
    , m: Position.int
    , n: IntInf.int
    , o: Real.real
    , p: LargeReal.real
    , q: Char.char
    , r: Word.word
    , s: Word8.word
    , t: Word32.word
    , u: Word64.word
    , v: LargeWord.word
    , w: Date.date
    , x: CharVectorSlice.slice
    , y: Substring.substring
    , z: Time.time
    }
end

datatype test_hash = Foo of int * string | Bar of {a: int, b: string}

structure Bar =
struct
  type t =
    { a: Bool.bool Option.option
    , b: Char.char List.list
    , c: int ref
    , d: Foo.t
    , e: unit
    }
  type bar = unit
  datatype bar = Bar of unit
end