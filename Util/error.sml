structure Error :> sig
  
  exception Error
  val parse : string -> 'a
  val runtime : string -> 'a
  val static : string -> 'a
end = struct

  exception Error
  
  fun error (flag:string) (s:string):'a = 
    (print (flag^" ERROR: "^s); print "\n"; raise Error)

  (* generate a parse error *)
  fun parse (s:string):'a = error "PARSE" s

  (* generate a runtime error *)
  fun runtime (s:string):'a = error "RUNTIME" s

    (* generate a static (type checking) error *)
  fun static (s:string):'a = error "STATIC" s
               
end
