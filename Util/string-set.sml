
(* instantiate sets of strings *)

structure StringSet = RedBlackSetFn (struct
                                       type ord_key = string
                                       val compare = String.compare
                                     end)
