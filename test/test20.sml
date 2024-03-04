structure A =
struct
  datatype 'a foo = Foo of 'a B.t
  type 'b B_t = 'b foo
  datatype 'a t = T of 'a B_t
end
structure B =
struct
  datatype 'a bar = Bar of 'a A.t
  type 'b A_t = 'b bar
  datatype 'a t = T of 'a A_t
end
