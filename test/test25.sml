val () =
  let
    type t = word
    datatype t = Foo of int | Bar of string * t
  in
    print "expression\n"
  end


structure Module =
struct
  val hello =
    let
      type hello = string
      val hello: hello = "hello"
    in
      hello
    end
end

val _ =
  1
  +
  List.hd
    (List.map
       (fn a =>
          2
          +
          ((fn b =>
              a
              +
              (b
               +
               (let
                  type t = int
                  val result: t = 4
                in
                  result
                end))) 3)) [1, 2, 3])