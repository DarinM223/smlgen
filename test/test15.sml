datatype t = TA of (t * string * t) | TB of int
datatype result = ResultC of t | ResultD of string list