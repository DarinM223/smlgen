structure Foo =
struct datatype foo = Bar of Bar.bar | Hello datatype notthis = Blah | Bleargh end

structure Bar =
struct datatype bar = Foo of Foo.foo | World datatype northis = A | B end

datatype no = No