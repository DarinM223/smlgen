structure Bar = struct
  datatype 'a t = Bar of { a : int, b : 'a }
  datatype bar = Bar' of int * int t
end

structure Foo = struct
  datatype 'a t = Foo of int Bar.t * 'a Bar.t * Bar.bar * 'a t | Nil
end

val _ = print (Foo.show Int.toString (Foo.Foo (Bar.Bar {a = 1, b = 2}, Bar.Bar {a = 3, b = 4}, Bar.Bar' (5, Bar.Bar {a = 6, b = 7}), Foo.Nil)) ^ "\n")