structure Foo = struct
  datatype 'a t = Foo of int Bar.t * 'a Bar.t * 'a t | Nil
end

structure Bar = struct
  datatype 'a t = Bar of { a : int, b : 'a }
end