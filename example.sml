structure A =
struct
  datatype 'a foo = Foo of B.t
  type 'a B_t = 'a foo
  datatype 'a t = T of 'a B_t
end
structure B =
struct
  datatype 'a bar = Bar of A.t
  type 'a A_t = 'a bar
  datatype 'a t = T of 'a A_t
end
