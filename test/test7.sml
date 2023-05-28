type person = { a: int, b: string, c: int * string * {d: int * int, e: string list}}

type 'a foo = 'a list list * 'a * {a : int list, b: string}

type ('a, 'b) bar = 'a * 'b * int