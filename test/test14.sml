infix & *` +`

structure Lam =
struct
  type varname = int
  datatype exp =
    Var of varname
  | App of exp * exp
  | Lam of varname * exp
  | Let of varname * exp * exp
end

structure Typ =
struct
  type qname = string

  datatype typ =
    TVar of tv ref
  | QVar of qname
  | TArrow of typ * typ
  and tv =
    Link of typ
  | Unbound of string
end