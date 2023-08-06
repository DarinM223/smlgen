smlgen
======

A code generator for Standard ML that generates boilerplate functions for
things like converting types to strings, comparing types, etc.

Building
--------

After cloning the repo, run:

```
git submodule update --init --recursive
```

to clone the submodules, then run:

```
mlton smlgen.mlb
```

to build the project in MLton.

To build the project in Poly/ML, run:

```
polyc build.sml -o smlgen
```

Running
-------

The first argument is the path of the Standard ML
file to run the generator on. The next arguments are
the type name and generators to run on the type separated by colons.

```
./smlgen foo.sml Ast.Str.strdec:g Parser.t:u Person.t:s
```

You can combine generators for a type like:
```
Ast.t:gu
```

The characters corresponding to each generator are listed below:

| Option |        Generator                                |
|--------|-------------------------------------------------|
|   u    | Functional record update                        |
|   g    | [Generic](https://github.com/DarinM223/generic) |
|   s    | Show                                            |
|   c    | Compare                                         |

smlgen will prompt you for every type name that matches to generate code for that type. It will then overwrite the file with the formatted and generated code.

In order to check the output without overwriting the file, you can pass in a `--test` option before the first argument to write to the filename with `.test` appended to it. So:

```
./smlgen --test file.sml ...
```

will create a `file.sml.test` file in the same directory as `file.sml`.

smlgen also allows you to generate many commonly used files for things like array literal syntax, printf syntax, etc. To generate these files, run:

```
./smlgen -gen <generator>
```

The list of file generators is shown below:

| Generator |             Description                                                 |
|-----------|-------------------------------------------------------------------------|
| fru       | [Functional record update](http://www.mlton.org/FunctionalRecordUpdate) |
| fold      | [Fold](http://www.mlton.org/Fold)                                       |
| fold01n   | [Fold01N](http://www.mlton.org/Fold01N)                                 |
| product   | [Product](http://www.mlton.org/ProductType)                             |
| printf    | [Printf](http://www.mlton.org/Printf)                                   |
| num       | [Numeric literals](http://www.mlton.org/NumericLiteral)                 |
| literal   | [Array & Vector literals](http://www.mlton.org/ArrayLiteral)            |
| optarg    | [Optional arguments](http://www.mlton.org/OptionalArguments)            |

smlgen also allows you to generate an initial project with the `-proj` option. For example, to generate
an initial project named `hello`, run:

```
./smlgen -proj hello
```

And it will create a `hello` directory with initial project files.

Testing
-------

To run the tests, run:

```
sh test.sh
```

in the project directory. It should list the number of succeeded and failed tests and
the diff between the generated code and the expected code for each failed test.

Current limitations
-------------------

Right now, the generic generation doesn't handle constructor names that conflict
with the existing generic constructors like `T` or `C1`, etc. So this:

```sml
datatype 'a t = T of 'a * 'a t * int t * string t (* BAD *)
```

will generate a function that doesn't compile. Instead, rename the constructor
to not conflict:

```sml
datatype 'a t = T' of 'a * 'a t * int t * string t
```

All of the generator functions handle some types of polymorphic recursive use inside its definition. In the above example, the constructor of `'a t` contains monomorphic uses of `t` (`int t` and `string t`), and a naive recursive function will not work with these, since it will unify `'a` with either `int` or `string`.
The generator functions work around this by creating separate functions for `int t` and `string t`.
However, if the type itself grows infinitely, the generator will skip the type
and print the message `Max type size limit exceeded`. So a generator for something like this cannot be done:

```sml
datatype 'a t = T' of 'a * 'a list t (* BAD *)
```

You may hit the maximum type size limit error unintentionally, from having a very large record or tuple.
In that case you can increase the maximum type size with the `-maxsize` flag. For example:

```
./smlgen file.sml ... -maxsize 1000
```

will set the max type size limit to 1000. The default max type size is set at 100.