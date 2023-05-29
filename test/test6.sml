structure Bar = struct
  datatype 'a t = Bar of { a : int, b : 'a }
  datatype bar = Bar' of int * int t
end

structure Foo = struct
  datatype 'a t = Foo of int Bar.t * 'a Bar.t * Bar.bar * 'a t | Nil
  type foo = {a: int * int, b: int t}
end