(*
  The different types that will be given to you by the parser.
*)
structure AbSyn = struct

  type id = string

  (*
     Types are Integer types, Real Types, String types, Tuple Types,
     Record Types and Function types i.e. Int -> Int is a tuple of (Int, Int)
     Units are represented as Tuple_t [].
  *)

  (* can't use type because it is a reserved word *)
  datatype typ = Int_t | Real_t | String_t | Char_t | Id_t of id |
                 Tuple_t of typ list | Record_t of (id * typ) list |
		 Fn_t of (typ * typ) | DataTyp_t of string | Ref_t of typ | Wrong_t 

  type funrec = {name:id, arg: id, arg_typ: typ, ret_typ:typ}

  datatype const = Int_c of int | Real_c of real |
                   String_c of string | Char_c of char

  (* in order they represent the binary operators
     "+", "*", "-", "=", "^", ">", "<", ">=", "<=" *)
  datatype binop = Plus | Times | Minus | Equal | Concat
  | GreaterThan | LessThan | GreaterThanEq | LessThanEq

  datatype constructors = Nil | None | True | False | Cons | Some

  (* representing "~" and "not" *)
  datatype unop = Neg | Not | isNil | isSome | isCons | isTrue | isFalse 
   | isNullary | isValueCarry | isNone | valueOf 

  (* Examples of each expression, declaration and pattern
     are commented besides each type
   *)
  datatype exp = Const_e of const | (* 5, "string", etc *)
                 Id_e of id | (* any variable identifier*)
                 Fn_e of (id*typ*exp) | (* fn (s:string) => 6 *)
                 App_e of (exp*exp) |   (* increment(6) *)
                 Unop_e of (unop * exp) |  (* not true *)
                 Binop_e of (exp*binop*exp) |  (* 5 + 5 *)
                 Tuple_e of (exp list) |  (* (5,4,4,3) *)
                 Ith_e of (int*exp) |     (* #1 (3,4,5) *)
                 If_e of (exp * exp * exp) | (* if e1 then e2 else e3 *)
                 Record_e of ((id*exp) list) | (* {name="greg", major="cs"} *)
                 (* fields carry an extra argument, the (sorted) type of
                  * the argument it is applied to *)
                 Field_e of (id*exp*(typ option ref)) | (* #n {n="greg"} *)
                 DataCon_e of (id*(exp option)) | (* Int(4) or Int_t *)
                 Case_e of (exp*(pat*exp)list) |  (* case x of 5 => x _ => 4 *)
                 Let_e of (decl list*exp) | (* let val x = 4 in x + x end; *)
                 Deref_e of (exp) | (* !x *)
                 Assign_e of (exp * exp) | (* x := 3 *)
                 Ref_e of (exp) | (* ref x *)
                 Error_e of (exp)


  and decl = Val_d of (pat*exp) |  (* val (x,y) = (5,2) *)
             Fun_d of (funrec*exp) (* fun inc(i:int):int = i + 1 *)


  and pat = Wild_p | (* _ *)
            Id_p of id | (* any variable identifier*)
            Const_p of int | (* 5 *)
            DataCon_p of (id*pat option) | (* same as DataCon_e *)
            Tuple_p of pat list | (* same as Tuple_e *)
            Record_p of (id*pat) list (* same as Record_e *)

  datatype top_level = Exp_t of exp
                     | Decl_t of decl list

end
