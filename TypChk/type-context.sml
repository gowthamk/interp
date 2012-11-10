signature TYPE_CONTEXT = sig

  type context
  val empty_env : context
  val add_var : context * AbSyn.id * AbSyn.typ -> context
  val lookup_var : context * AbSyn.id -> AbSyn.typ option
  val add_type : context * AbSyn.id * AbSyn.typ -> context
  val lookup_type : context * AbSyn.id -> AbSyn.typ option
  (* second evironment takes precedence during conflicts *)
  val union_env : context * context -> context
  (* last environment gets precedence *)
  val union_envs : context list -> context

end

structure TypeContext :> TYPE_CONTEXT = struct

  structure SM = StringMap

  type context = (AbSyn.typ SM.map * AbSyn.typ SM.map)

  (* Built-in datatypes *)
  val dataTypes = ["intlist", "bool" , "intoption"]

  val empty_type_env =
     foldl (fn (name, env) => SM.insert (env,name,AbSyn.DataTyp_t name))
           SM.empty dataTypes

  val empty_env = (SM.empty, empty_type_env)

  fun add_var ((varCtext,typeCtext),var,vtype) : context =
    (SM.insert (varCtext,var,vtype), typeCtext)

  fun lookup_var ((varCtext,_),var) : AbSyn.typ option =
    SM.find (varCtext,var)

  fun add_type ((varCtext,typeCtext),obj,otype) : context =
    (varCtext, SM.insert (typeCtext,obj,otype))

  fun lookup_type ((_,typeCtext),obj) : AbSyn.typ option =
    SM.find (typeCtext,obj)

  fun union_env ((varCtext1,typeCtext1),(varCtext2,typeCtext2)) =
    (SM.unionWith (fn (x,y)=>y) (varCtext1, varCtext2),
     SM.unionWith (fn (x,y)=>y) (typeCtext1, typeCtext2))

  fun union_envs l = foldr union_env empty_env l

end
