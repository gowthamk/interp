signature DATA_TYPES = sig

  val isNullCons : string -> bool option
  val consResTyp : string -> AbSyn.typ
  val consArgTyp : string -> AbSyn.typ

end

structure DataTypes :> DATA_TYPES = struct

  structure SM = StringMap

  structure A = AbSyn

  (* construct a map containing the primitive data constructors *)
  val dataCons =
    foldl (fn ((x,y),m) => SM.insert (m,x,y)) SM.empty
       [("Nil",{res_typ=A.DataTyp_t "intlist",
                arg_typ=NONE}),
        ("Cons",{res_typ=A.DataTyp_t "intlist",
                 arg_typ=SOME (A.Tuple_t [A.Int_t,
                                          A.DataTyp_t "intlist"])}),
        ("true",{res_typ=A.DataTyp_t "bool",
                 arg_typ=NONE}),
        ("false",{res_typ=A.DataTyp_t "bool",
                  arg_typ=NONE}),
        ("NONE",{res_typ=A.DataTyp_t "intoption",
                 arg_typ=NONE}),
        ("SOME",{res_typ=A.DataTyp_t "intoption",
                 arg_typ=SOME(A.Int_t)})]

  (* check to see if a constructor exists and if it is nullary *)
  fun isNullCons (id:string):bool option =
    case SM.find (dataCons,id) of
      NONE => NONE
    | SOME {arg_typ,...} => SOME (not (Option.isSome (arg_typ)))

  (* return the result type of a constructor *)
  fun consResTyp (id:string):A.typ =
    case SM.find (dataCons,id) of
      NONE => Error.static ("Undefined constructor "^id)
    | SOME {res_typ,...} => res_typ

  (* return the argument type of a construct with argument *)
  fun consArgTyp (id:string):A.typ =
    case SM.find (dataCons,id) of
      SOME {arg_typ=SOME t,...} => t
    | _ => Error.static ("Undefined constructor "^id)

end
