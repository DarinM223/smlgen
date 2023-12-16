structure FOO = struct
  datatype t = Cons of char * t list | Atom of char
end