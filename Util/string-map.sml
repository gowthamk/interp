
(* Instantiate maps on strings *)

structure StringMap = RedBlackMapFn (struct
                                       type ord_key = string
                                       val compare = String.compare
                                     end)
