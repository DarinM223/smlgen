datatype 'a person = Person of { name: 'a, age: int, address: { name: 'a, locations: string list } }

datatype 'a foo = A of 'a * int * string | B of ('a * 'a) * {a : int, b : ('a * string)} | C of 'a | D

datatype bar = Bar