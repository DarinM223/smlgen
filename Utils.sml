structure Utils =
struct
  fun capitalize s =
    case String.explode s of
      c :: cs => String.implode (Char.toUpper c :: cs)
    | _ => s

  structure SCC =
  struct
    type state = {index: int, lowlink: int, onStack: bool}

    fun scc tbl graph nodes k =
      let
        val stack: int list ref = ref []
        val index = ref 0
        infix ::=
        fun pop () =
          case !stack of
            w :: t => w before (stack := t)
          | [] => raise Fail "cannot pop"
        fun !! a = IntHashTable.lookup tbl a
        fun a ::= b = IntHashTable.insert tbl (a, b)
        fun modify a f =
          a ::= f (!!a)

        fun popUntil v =
          let
            val w = pop ()
          in
            if w <> v then
              ( modify w (fn w =>
                  {index = #index w, lowlink = #lowlink w, onStack = false})
              ; w :: popUntil v
              )
            else
              [w]
          end

        fun strongconnect v =
          ( v ::= {index = !index, lowlink = !index, onStack = true}
          ; index := !index + 1
          ; stack := v :: !stack
          ; List.app
              (fn w =>
                 if not (IntHashTable.inDomain tbl w) then
                   ( strongconnect w
                   ; modify v (fn {index, lowlink, onStack} =>
                       { index = index
                       , lowlink = Int.min (lowlink, #lowlink (!!w))
                       , onStack = onStack
                       })
                   )
                 else
                   modify v (fn {index, lowlink, onStack} =>
                     { index = index
                     , lowlink = Int.min (lowlink, #index (!!w))
                     , onStack = onStack
                     })) (graph v)
          ; if #lowlink (!!v) = #index (!!v) then k (popUntil v) else ()
          )
      in
        List.app
          (fn v =>
             if not (IntHashTable.inDomain tbl v) then strongconnect v else ())
          nodes
      end
  end
end

(* exception Beta
val graph: int list IntHashTable.hash_table = IntHashTable.mkTable (100, Beta)
val () = IntHashTable.insert graph (0, [1, 2])
val () = IntHashTable.insert graph (1, [1, 0])
val () = IntHashTable.insert graph (2, [1])
val () = IntHashTable.insert graph (3, [4, 5])
val () = IntHashTable.insert graph (4, [3, 5])
val () = IntHashTable.insert graph (5, [])
val () =
  Utils.SCC.scc (IntHashTable.mkTable (100, Beta)) (IntHashTable.lookup graph)
    [0, 1, 2, 3, 4, 5]
    (fn l => (List.app (fn i => print (Int.toString i ^ ", ")) l; print "\n")) *)