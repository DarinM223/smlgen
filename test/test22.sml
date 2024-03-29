structure Foo = struct
    datatype foo = Foo of { value : foo' option }
    withtype foo' = { opt1 : foo option, opt2 : foo'' option }
    and foo'' = Bar.bar * Foo.foo
end

structure Bar = struct
    datatype bar = Bar of Foo.foo''
end
