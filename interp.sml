structure MiniML :> 
   sig
      val interpreter : unit -> unit
   end = 

struct
  structure T = TypeCheck
  structure TC = TypeContext
  structure A = AbSyn
  structure PP = PrettyPrinter
  structure TypePP = TypePP

  exception UnboundVariable of string
  exception InternalError of string

(* values *)

datatype conId = True_v | False_v | Nil_v | None_v | Some_v | Cons_v

datatype env = Env of A.exp -> value 
and
 value =  
    Int_v of int     (* an int or a char *)
  | Real_v of real   (* a real *)
  | String_v of string (* a string *)
  | Char_v of char (* a char *)
  | Tuple_v of value list (* a tuple *)
  | Record_v of (A.id * value) list (* a record *)
  | DataCon_v of (conId * (value option)) (* constructor *)
  | Closure_v of A.exp * A.id * (env ref) (* "code" * arg * runtime env *)
  | Ref_v of (value ref)


(* Used to generate "fresh" variable names during pattern match
* compilation. *)
    local
        val counter = ref 0
    in
        fun gensym() =
            let val c = Int.toString(!counter)
            in
                counter := (!counter) + 1;
                "%temp"^c
            end
    end

  (* Helper functions *)

    (* get the cunop from constructors *)
  fun constr2cunop ( c:A.constructors)  = 
      ( case c of 
          A.Nil   => A.isNil
        | A.None  => A.isNone
        | A.True  => A.isTrue
        | A.False => A.isFalse
        | A.Some  => A.isSome
        | A.Cons  => A.isCons)

    (* Map a nullary data constructor to an integer value. *)
  fun nullary_datacon_tag x =
        case x of
            "NONE" => A.None
          | "Nil" => A.Nil
          | "true" => A.True
          | "false" => A.False
          | _ => raise InternalError("unknown constructor "^x)

    (* map a value-carrying data constructor to an integer value *)
  fun value_datacon_tag x =
        case x of
            "Cons" => A.Cons
          | "SOME" => A.Some
          | _ => raise InternalError("unknown constructor "^x)

    (* sort for records *)
  fun field_sort(fs) =
        ListMergeSort.sort (fn ((x:A.id,_),(y:A.id,_)) => x > y) fs

  (* Printing *)
  fun printList(l) = let fun collect(l,acc) = (case l of
						  DataCon_v(Cons_v, SOME(Tuple_v [v,r])) =>  
						     collect(r,(v:: acc)) 
						| _ => acc)
			 val vs = collect(l,[])
		     in "[" ^ (List.foldl
                                  (fn (v,acc) => (value2string(v) ^ " " ^ acc))
                                  ""
                                  vs) ^ "]"
		     end

  and value2string(v':value):string = 
      case v' of
          Int_v(i) => Int.toString i
        | Real_v(r) => Real.toString r
        | String_v (s) => s
        | Char_v (c) => Char.toString c
        | Ref_v v => "ref " ^ value2string(!v)
        | Record_v fs => "{" ^ (List.foldl 
                                   (fn ((id,v),acc) => (id ^ " = " ^ value2string(v) ^ " ") ^ acc)
				   ""
                                   fs)  ^ "}"
        | Tuple_v (tl) => let fun conv(nil) = "()" (*error "empty tuple"*)
                               |  conv(v::nil) = value2string(v)
                               |  conv(v::rest) = value2string(v)^","^conv(rest)
			   in "("^(conv(tl))^")"
			  end
        | Closure_v(e, id, env) => "Closure("^(PP.ppExp e)^")"
        | DataCon_v(True_v,_) => "true"
        | DataCon_v(False_v,_) => "false"
        | DataCon_v(Nil_v,_) => "Nil"
        | DataCon_v(None_v,_) => "NONE"
        | DataCon_v(Cons_v,SOME s) => printList(v')
        | DataCon_v(Some_v,SOME s) => "SOME" ^ value2string(s)
        | _ => Error.runtime("Attempting to print a non-value")

  fun print_value(v:value):unit =  print(value2string(v))

  (* Environments *) 

  val empty_env = Env(fn x => (case x of 
				  A.Id_e(var) => Error.runtime("Variable : "^ var ^ " not bound")
				| _ => Error.runtime("Attempting to lookup a non-variable")))

  fun lookup(x,e) = let val Env(env) = e in env(x) end

  fun add_env(x,v,e) = let val a = (case x of
				       A.Id_e(a) => a
				     | _ => Error.runtime("Attempting to lookup a non-variable"))
		       in Env(fn y => let val b = (case y of
						      A.Id_e(b) => b
						    | _ => Error.runtime("Attempting to lookup a non-variable"))
				      in if a = b then v else lookup(y,e)
				      end)
		       end

  (*-------------- Engine ---------------*)

  (* The toplevel environment: keep a type context for the type of the toplevel
   * identifiers, and value bindings 
   *)
  type global_env = {type_context: TC.context, topLevelEnv: env }

  (* reconstruct a string from a list of tokens, inserting spaces *)
  fun reconstructString (sl:string list):string =
    ListFormat.fmt {final="",init="",fmt=fn x => x,sep=" "} sl

  (* evaluator *)

  fun eval_be(v1:value,bop:A.binop,v2:value): value =
   case bop of 
     A.Plus => (case v1 of 
                   Int_v(i1) => 
                      ( case v2 of 
                          Int_v(i2) => Int_v( i1 + i2)
                        | _ => Error.runtime("Binop Plus: expect Int (2)"))
                 | Real_v(i1) => 
                      ( case v2 of 
                          Real_v(i2) => Real_v( i1 + i2)
                        | _ => Error.runtime("Binop Plus: expect Real (2)"))
                 | _ => Error.runtime("Binop Plus: expect Real (1)"))
   | A.Times => (case v1 of 
                   Int_v(i1) => 
                      ( case v2 of 
                          Int_v(i2) => Int_v( i1 * i2)
                        | _ => Error.runtime("Binop Times: expect Int (2)"))
                 | Real_v(i1) => 
                      ( case v2 of 
                          Real_v(i2) => Real_v( i1 * i2)
                        | _ => Error.runtime("Binop Times: expect Real (2)"))
                 | _ => Error.runtime("Binop Times: expect Real (1)"))
   | A.Minus => (case v1 of 
                   Int_v(i1) => 
                      ( case v2 of 
                          Int_v(i2) => Int_v( i1 - i2)
                        | _ => Error.runtime("Binop Minus: expect Int (2)"))
                 | Real_v(i1) => 
                      ( case v2 of 
                          Real_v(i2) => Real_v( i1 - i2)
                        | _ => Error.runtime("Binop Minus: expect Real (2)"))
                 | _ => Error.runtime("Binop Minus: expect Real (1)"))
   | A.Equal =>
	(case v1 of
	    Int_v(i1) => 
	       ( case v2 of 
		    Int_v(i2) => if i1 = i2 then 
		       DataCon_v(True_v,NONE)
				 else DataCon_v(False_v,NONE)
		  | _ => Error.runtime("Binop Equal: operand types mismatch (Int)"))
	  | String_v(i1) => 
	       ( case v2 of
		    String_v(i2) => 
		       if i1 = i2 then 
			  DataCon_v(True_v,NONE)
		       else DataCon_v(False_v,NONE)
		  | _ => Error.runtime("Binop Equal: wrong operand types"))
	  | _ => Error.runtime("Can only compare ints and strings for equality"))
   | A.Concat => (case v1 of 
		     String_v(i1) => 
			( case v2 of 
			     String_v(i2) => String_v( i1 ^ i2)
			   | _ => Error.runtime("Binop Concat: expect Int (2)"))
		   | _ => Error.runtime("Binop Concat: expect Int (1)"))
   | A.LessThan => 
	(case v1 of 
             Int_v(i1) => 
                ( case v2 of 
                    Int_v(i2) =>
                       if i1 < i2 then 
                          DataCon_v(True_v,NONE)
		       else DataCon_v(False_v,NONE)
                  | _ => Error.runtime("Binop LessThan: expect Int (2)"))
           | _ => Error.runtime("Binop LessThan: expect Int (1)"))
   | A.GreaterThan => 
	(case v1 of 
             Int_v(i1) => 
                ( case v2 of 
                    Int_v(i2) =>
                       if i1 > i2 then 
                          DataCon_v(True_v,NONE)
		       else DataCon_v(False_v,NONE)
                  | _ => Error.runtime("Binop GreaterThan: expect Int (2)"))
           | _ => Error.runtime("Binop GreaterThan: expect Int (1)"))
   | A.GreaterThanEq => (case v1 of 
			    Int_v(i1) => 
			       ( case v2 of 
				    Int_v(i2) =>
				       if i1 >= i2 then 
					  DataCon_v(True_v,NONE)
				       else DataCon_v(False_v,NONE)
				  | _ => Error.runtime("Binop GreaterThanEq: expect Int (2)"))
			  | _ => Error.runtime("Binop GreaterThanEq: expect Int (1)"))
   | A.LessThanEq => 
	(case v1 of 
             Int_v(i1) => 
                ( case v2 of 
                    Int_v(i2) =>
                       if i1 <= i2 then 
                          DataCon_v(True_v,NONE)
		       else DataCon_v(False_v,NONE)
                  | _ => Error.runtime("Binop LessThanEq: expect Int (2)"))
           | _ => Error.runtime("Binop LessThanEq: expect Int (1)"))

  fun eval_ue(uop:A.unop,v:value): value =
    (case uop of
       A.Not =>
          (case v of
              DataCon_v(True_v,NONE) => DataCon_v(False_v,NONE)
            | DataCon_v(False_v,NONE) => DataCon_v(True_v,NONE)
            | _ => Error.runtime("type mismatch for Bool (1)") )
     | A.Neg =>
          (case v of
              Int_v(i) => Int_v(~i)
            | _ => Error.runtime("type mismatch for Int (1)"))
     | A.isNil =>
	  (case v of
	      DataCon_v(Nil_v,NONE) => DataCon_v(True_v,NONE)
            | _ => DataCon_v(False_v,NONE))
     | A.isNullary =>
         (case v of
	     DataCon_v(Nil_v,NONE) => DataCon_v(True_v,NONE)
	   | DataCon_v(None_v,NONE) => DataCon_v(True_v,NONE)
	   | DataCon_v(True_v,NONE) => DataCon_v(True_v,NONE)
	   | DataCon_v(False_v,NONE) => DataCon_v(True_v,NONE)
	   | _ => DataCon_v(False_v,NONE))
     | A.isNone => 
	  (case v of
	      DataCon_v(None_v,NONE) => DataCon_v(True_v,NONE)
	    | _ => DataCon_v(False_v,NONE))
     | A.isValueCarry => 
	  (case v of
	     DataCon_v(Some_v,_) => DataCon_v(True_v,NONE)
	   | DataCon_v(Cons_v,_) => DataCon_v(True_v,NONE)
	   | _ => DataCon_v(False_v,NONE))
     | A.valueOf =>
	  (case v of
	     DataCon_v(_,SOME(x)) => x
	   | _ => Error.runtime("Cannot deconstruct a non value-carrying constructor"))
     | A.isSome =>
	  (case v of
	      DataCon_v(Some_v,SOME x) => DataCon_v(True_v,NONE)
            | _ => DataCon_v(False_v,NONE))
     | A.isCons =>
	  (case v of
	      DataCon_v(Cons_v,SOME x) => DataCon_v(True_v,NONE)
            | _ => DataCon_v(False_v,NONE))
     | A.isTrue =>
	  (case v of
	      DataCon_v(True_v,NONE) => DataCon_v(True_v,NONE)
            | _ => DataCon_v(False_v,NONE))
     | A.isFalse =>
	  (case v of
	      DataCon_v(False_v,NONE) => DataCon_v(True_v,NONE)
            | _ => DataCon_v(False_v,NONE)))


  (* Pattern matching *)
  (* Desugars into 1. Function Applications and 2. if-else stmts *)
  fun pat_compile (p:A.pat) (root:A.exp) (ok:unit->A.exp)
        (fail:unit->A.exp) : A.exp =
        case p of
            A.Wild_p => ok()
            (* wild patterns alway succeed *)
          | A.Id_p(x) => (* val x = 2 *)
              A.App_e(A.Fn_e(x,A.Id_t("patType"),ok()),root)
          | A.DataCon_p(x,NONE) => 
            (* generate code to test that the root is is equal to
             * the appropriate nullary constructor *)
             (* x_cc is unary expression that tests if its arg is
                the constructor x *)
               let val x_cc = constr2cunop(nullary_datacon_tag x)
             (* First test if root is nullary. Then test if that 
                nullary cons is what we are looking for *)
		   val term =  A.If_e(A.Unop_e(A.isNullary, root),
				      A.If_e(A.Unop_e(x_cc, root), ok(), fail()),
				      fail())
	       in term
               end
          | A.DataCon_p(x,SOME(p')) => 
                (* generate code to test that the root is is a value-carrying tuple *)
             let val x_cc = constr2cunop(value_datacon_tag x) 
                (* Checks if root is non-nullary constructor *)
                 val term = A.If_e( A.Unop_e(A.isValueCarry, root),
                (* Then check if constructors actually match *)
				   A.If_e(A.Unop_e(x_cc,root),
                (* A.valueOf generates code to get unroll root once *)
                (* Next p' is unrolled and corresponding vals are assigned *)
					  pat_compile p' (A.Unop_e(A.valueOf,root)) ok fail,
					  fail()) ,
				   fail())
	     in term
             end
          | A.Record_p(idps) => 
                (* sort the record and then dispatch against different fields *)
                let val sorted_idps = field_sort idps
                    val x = gensym()
                    fun loop (es) =
		          case es of
                            [] => ok()
                          | (id,p)::rest => pat_compile p (A.Field_e(id,A.Id_e(x),ref NONE))
			                                (fn () => loop(rest))
                                                        fail
		in
                    A.App_e(A.Fn_e(x,A.Id_t("pat"),loop(sorted_idps)),root)
                end
          | A.Const_p(i) => 
            (* generate code to test that root is equal to i *)
            let val term = A.If_e(A.Binop_e(A.Const_e(A.Int_c(i)),A.Equal,root),
                                  ok(),fail())
            in
              term
            end
          | A.Tuple_p(ps) => 
                (* generate code to test each pattern from left-to-right
                 * against the root. *)
            let fun loop (es,i) =
              case es of
                [] => ok()
                | p::rest => pat_compile p (A.Ith_e(i,root)) (fn () => loop(rest,i+1)) fail
            in
              loop(ps,1)
            end
    (* compile a list of cases "p1=>e1 | p2=>e2 | ... | pn=>en"
     * into an appropriate test expression.  x is an identifier bound to the value
     * being tested, and cases is the list of patterns and expressions
     * to be compiled. *)
    and comp_cases (x:A.id) (cases : (A.pat*A.exp) list) : A.exp =
        case cases of
            [] => 
                (* generate code for an inexhaustive match *)
                A.Error_e(A.Const_e(A.String_c("Match problem")))
          | (p,e)::rest =>
              pat_compile p (A.Id_e(x)) (fn _ => e) (fn _ => comp_cases x rest)
                (* compile pattern p -- if the resulting code
                 * succeeds in the pattern match, then evaluate
                 * e, otherwise continue with the next pattern
                 * in the list. *)

 (* Evaluator *)

 fun patMatch(e,env) =
     (case e of
       A.Let_e(A.Val_d(p,e1)::d,e2) =>
          let 
            val let1 = A.Let_e(d,e2)
            val root = e1
            val ok   = fn _ => let1
          in
            eval(pat_compile p root ok ok,env)
          end
       | A.Case_e(e,cases) => let val eid = gensym()
				  val compiledPat = A.App_e(A.Fn_e(eid,A.Id_t("pat"),comp_cases eid cases),e)
			      in eval(compiledPat,env)
			      end
       | _ => Error.runtime("Ill-formed pattern" ^ PP.ppExp(e)))

and eval(e,env) =
    (case e of
	A.Const_e c => (case c of
			   A.Int_c i => Int_v i
			 | A.Real_c r => Real_v r
			 | A.String_c s => String_v s
			 | A.Char_c c => Char_v c)
      | A.Id_e(x) => lookup(e,env)
      | A.Fn_e(id,ty,exp) => (*We don't evaluate under abstractions, 
        but capture the function definition in current environment.*)
        let
          val env_ref = ref env
        in
          Closure_v(exp,id,env_ref)
        end
      | A.App_e(f,arg) => 
          let 
            (*call by value. evaluate args first*)
            val v_arg = eval(arg,env) 
            (*Then get closure for f*)
            val v_f = eval(f,env)
          in
            case v_f of
            Closure_v(exp,id,env_ref) => 
              let val ref closed_env = env_ref in
                let val extended_closed_env = add_env(A.Id_e(id),v_arg,closed_env) in
                  eval(exp,extended_closed_env)
                end
              end
            | _ => Error.runtime("LHS of function application did not evaluate to a closure")
          end
      | A.Unop_e(uop,exp) => let val v = eval(exp,env)
			     in eval_ue(uop,v)
			     end
      | A.Binop_e(e1,bop,e2) => let val v1 = eval(e1,env)
				    val v2 = eval(e2,env) 
				in eval_be(v1,bop,v2)
				end
      | A.Tuple_e(exps) => 
          let
            fun loop (exps,env) = case exps of
              [] => []
              | e::rest => (eval(e,env))::loop(rest,env)
          in
            Tuple_v (loop(exps,env))
          end
      | A.Ith_e(i,e2) =>  let val v = eval(e2,env)
			   in (case v of
				  Tuple_v vs => (List.nth(vs,i-1))
				| _ => Error.runtime("attempting to select from a non-tuple"))
			   end
      | A.If_e(e1,e2,e3) => (*Evaluate guard and accordingly evaluate true and false branches*)
        let 
          val DataCon_v(guard,_) = eval(e1,env) 
        in
          case guard of
          True_v => eval(e2,env)
          | False_v => eval(e3,env)
          | _ => Error.runtime("If statement guard should be a bool value")
        end
      | A.Record_e(fields) => Record_v(List.map (fn(id,e) => (id,eval(e,env))) fields)
      | A.Field_e (id,e,ty) => Error.runtime("***not implemented eval:A.If_e***")

      | A.DataCon_e("true",NONE) => DataCon_v(True_v,NONE)
      | A.DataCon_e("false",NONE) => DataCon_v(False_v,NONE)
      | A.DataCon_e("Nil",NONE) => DataCon_v(Nil_v,NONE)
      | A.DataCon_e("NONE",NONE) => DataCon_v(None_v,NONE)
      | A.DataCon_e("Cons",SOME e) => DataCon_v(Cons_v,SOME(eval(e,env)))
      | A.DataCon_e("SOME",SOME e) => DataCon_v(Some_v, SOME(eval(e,env)))
      | A.DataCon_e (id,c) => 
	   (case c of
	       NONE => Error.runtime("Constructor cannot be reduced")
	     | SOME e => Error.runtime("1")(*let val v = eval(e,env)
			 in (case id of
				"SOME" => DataCon_v(Some_v,SOME(v))
			      | "Cons" => DataCon_v(Cons_v,SOME(v))
			      | _ => Error.runtime("Constructor mismatch"))
			 end*))
      | A.Case_e(test,ps) => patMatch(e,env)
      | A.Let_e([],e) => eval(e,env)
      | A.Let_e(A.Val_d(p,e1)::d,e2) => patMatch(e,env)
      | A.Let_e(A.Fun_d({name,arg,...},body)::d,e) =>
      (* Capture closure of function and bind it to name in extended env*)
	      let val closure = Closure_v(body,arg,ref env)
        in
          let val extended_env = add_env(A.Id_e(name),closure,env) in
            eval(A.Let_e(d,e),extended_env)
          end
	      end
      | A.Deref_e e => let val v = eval(e,env)
		       in  (case v of
			       Ref_v v => !v
			     | _ => Error.runtime("Trying to dereference a non-reference"))
		       end
      | A.Assign_e(e1,e2) => let val r = eval(e1,env)
				  val v = eval(e2,env)
			     in  (case r of
				     Ref_v x => (x := v; v)
				   | _ => Error.runtime("Illegal assignment"))
			     end
      | A.Ref_e(e) => Ref_v(ref (eval(e,env)))
      | A.Error_e(e) => (case eval(e,env) of
			    String_v s => (Error.runtime(s))
                          | _ => Error.runtime("Illegal argument to error")))


  fun evaluate(e,env) =
     let 
       val _ = TextIO.output (TextIO.stdOut, PP.ppExp(e));
       val v = eval(e,env)
     in   (print_value(v);
	   print "\n\n";
	   v)
     end
	  
  (* the interpreter entry point *)

  fun interpreter ():unit =
    let

      (* execute a command *)
      fun interpretCommand (s:string,genv:global_env):unit =
        let

          (* load an expression from a file *)
          fun load (f:string):unit =
            let
              val instream = TextIO.openIn (f)
              val parsed = Parser.parse(instream)
              val _ = TextIO.closeIn(instream)
              val newEnv = interpretParse (parsed,genv)
            in
              interpreter_loop (newEnv)
            end

          (* display the parse tree of an expression *)
          fun show_parse (rest:string list):unit =
            let
              val s = reconstructString (rest)
            in
              (case Parser.parseString (s) of
                NONE => ()
              | SOME (A.Exp_t (e)) => (print (PrettyPrinter.ppExp (e));
                                       print "\n")
              | SOME(A.Decl_t (ds))=>
                  (print (foldr (fn (d,s)=>(PrettyPrinter.ppDecl d)^s)"" ds);
                   print "\n"));
              interpreter_loop(genv)
            end

        in
          case Substring.getc (Substring.full (s)) of
            NONE => interpreter_loop (genv)
          | SOME (#":",ss) =>
              let
                val t = String.tokens Char.isSpace (Substring.string (ss))
              in
                case t of
                  ("l"::f::_) => load (f) 
                | ("p"::rest) => show_parse (rest)
		| ("t"::rest) => (interpretParse(Parser.parseString(reconstructString(rest)),genv:global_env);
				  interpreter_loop(genv))
                | ("s"::rest) => let val {type_context,topLevelEnv} = genv
				     val var = hd(rest)
				     val typ = TC.lookup_var(type_context,var)
				 in (case typ of
					NONE => print ("Variable " ^ var ^ " not in environment\n")
				      | SOME typ => print("The type of variable " ^ var ^ " is " ^
							  (TypePP.printType(typ)) ^ "\n");
   				     interpreter_loop(genv))
				 end
                | ("q"::_) => print "Bye.\n"
                | _ => (print "Command not recognized\n";
                        interpreter_loop (genv))
              end
          | _ => (print "Command not recognized\n";
                  interpreter_loop (genv))
        end

      (* if input is an expression or a declaration, parse
       * to obtain an abstract syntax tree
       *)
      and interpretParse (p:A.top_level option,genv:global_env) =
        let
          val {type_context,topLevelEnv} = genv
          fun typ_exp e =
            let
              val typ =  T.tcheck (type_context,e) 
                 handle Fail s => Error.static ("TypeChecker Failure: " ^ s)
              val _ = print ("Expression type : " ^ TypePP.printType (typ) ^ "\n\n")
	    in
		 typ
	    end
        in
          case p of
            NONE => genv
          | SOME(A.Decl_t([])) => genv
          (* evaluate an expression *)
          | SOME (A.Exp_t (exp)) => let val _ = (print (PrettyPrinter.ppExp (exp));
						 print "\n")                                  
					val _ = typ_exp(exp)
					val {type_context,topLevelEnv} = genv
					val v = evaluate(exp, topLevelEnv)
				    in genv
				    end
          | SOME (A.Decl_t (A.Val_d(A.Id_p(x),e1)::ds)) =>
              (* for declarations:  val x = e, evaluate e and push
               * it into the interpreter's environment, and then
               * enter a binding into both the type-checker's and
               * compiler's context *)
              let val typ = typ_exp(e1)
		 val {type_context,topLevelEnv} = genv
		 val _ = print("val " ^ x ^ " = ")
		 val v = evaluate(e1,topLevelEnv)
              in
                interpretParse
                 (SOME(A.Decl_t(ds)), {type_context = TC.add_var(type_context, x, typ),
				       topLevelEnv = add_env(A.Id_e(x),v,topLevelEnv)})
              end
          | SOME(A.Decl_t((d as A.Fun_d({name,arg,arg_typ,ret_typ},body))::ds))=>
              let val e = A.Let_e([d],A.Id_e(name))
                val typ = typ_exp(e)
		val {type_context,topLevelEnv} = genv
                val v = evaluate(e,topLevelEnv)
              in
                (interpretParse
                 (SOME(A.Decl_t(ds)),
                  {type_context = TC.add_var(type_context, name, typ),
		   topLevelEnv = add_env(A.Id_e(name),v,topLevelEnv)}))
              end
          (* we don't deal with all of the other forms of declarations at
           * the top-level *)
          | SOME (A.Decl_t(_)) =>
              (print "Sorry, only val and fun top-level declarations ";
               print "are supported in this version of Mini-ML.\n";
               genv)
        end

      (* the main interpreter loop. It passes the toplevel env around *)
      and interpreter_loop (genv:global_env):unit =
        let fun processLine ():unit =
          (case TextIO.inputLine (TextIO.stdIn) of
             NONE => ()
           | SOME c => (case c of
                          "" => ()
                         | s => if (String.isPrefix ":" s) (* if it is a command *)
                                  then interpretCommand (s,genv)
                                  else let
                                         val newEnv = interpretParse (Parser.parseString (s),genv)
                                       in
                                          interpreter_loop (newEnv)
                                      end))
        in
          TextIO.output (TextIO.stdOut, "MiniML> ");
          TextIO.flushOut (TextIO.stdOut);
          processLine () handle Error.Error  => interpreter_loop (genv)
        | e => (print "EXCEPTION: ";
                print (exnMessage (e));
                print "\n";
                interpreter_loop (genv))
        end
      val line = String.implode (List.tabulate (78,fn _ => #"-"))
    in
      print (concat [line,"\nCS502 MiniML interpreter\n"]);
      interpreter_loop ({type_context=TC.empty_env,topLevelEnv = empty_env})
    end

end
