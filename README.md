smlgen
======

A code generator for Standard ML that generates boilerplate functions for
things like converting types to strings, hashing types, etc.

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

to build the project.

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

| Option |        Generator         |
|--------|--------------------------|
|   u    | Functional record update |
|   g    | Generic                  |
|   s    | Show                     |

smlgen will prompt you for every type name that matches to generate code for that type. It will then overwrite the file with the formatted and generated code.

In order to check the output without overwriting the file, you can pass in a `--test` option before the first argument to write to the filename with `.test` appended to it. So:

```
./smlgen --test file.sml ...
```

will create a `file.sml.test` file in the same directory as `file.sml`.