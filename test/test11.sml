type t =
  { a: int
  , b: real
  , c: string
  , d: char
  , e: bool
  , f: int * real
  , g: string list
  , h: char ref * (bool * int) ref * {a: int, b: string} ref
  , i: int ref ref ref
  , j: unit * unit * {a: unit, b: unit}
  }