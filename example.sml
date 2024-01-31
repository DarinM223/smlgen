structure Foo =
struct datatype foo = Bar of Bar.bar | Hello datatype notthis = Blah | Bleargh end

structure Bar =
struct datatype bar = Foo of Foo.foo | World datatype northis = A | B end

datatype no = No

structure A =
struct datatype a = B of int * B.a and c = C of string and d = real end

structure B = struct datatype a = B of int * A.a and c = C of string end