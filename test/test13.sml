datatype 'a t = T' of 'a * 'a list t

datatype 'a t = T' of ('a * 'a) t

datatype 'a t = T' of ('a * 'a * 'a * 'a * 'a) list t

datatype ('a, 'b) t = T' of (('a * 'a) list, 'b * 'b) t

datatype 'a t = T' of { a: 'a } t

(* This should work *)
datatype 'a t = T' of 'a t

(* This should also work *)
datatype ('asuperextremelylongtypevariablethattakesupalotofcharacters, 'inordertotestthatthemaximumtypevariablesizeisnotbasedon, 'thestringlengthoftheprintextype, 'thiswouldnotworkotherwiseifthemaxtypevariablelengthisgreaterthanonehundredcharacterslong) t =
  T' of ('asuperextremelylongtypevariablethattakesupalotofcharacters, 'inordertotestthatthemaximumtypevariablesizeisnotbasedon, 'thestringlengthoftheprintextype, 'thiswouldnotworkotherwiseifthemaxtypevariablelengthisgreaterthanonehundredcharacterslong) t