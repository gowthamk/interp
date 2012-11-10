structure TypePP =

struct
   open AbSyn
   structure P = PrettyPrint
      
   fun sep (pp:P.ppstream) (s:unit->unit) (l:(unit->unit) list):unit =
      case l of
        [] => ()
      | [x] => x ()
      | (x::xs) => (x (); s (); sep pp s xs)

    val max_prec = 999;

    val empty_senv : string list = []
    fun next_var chars =
	case chars of
	    [] => ""
	  | hd::tl =>
		if (hd < #"z") then implode(chr(ord(hd)+1)::tl)
		else implode(#"a"::chars)

    fun push_var (senv: string list):string list =
	case senv of
	    [] => ["a"]
	  | hd::tl => (next_var (explode hd))::senv

    fun prec(typp:typ):int = 2

    fun typ2s (pp:P.ppstream) (p:int) (senv:string list) (typp:typ):unit = let
      fun begin ():unit = P.begin_block pp P.INCONSISTENT 0
      fun stop ():unit = P.end_block pp
      fun brI ():unit = P.add_break pp (1,2)
      fun br ():unit = P.add_break pp (1,0)
      fun str (s:string):unit = P.add_string pp s
      val p' = prec(typp)
      val e2s = typ2s pp p'
      fun s pp =
        case typp of
	  Int_t => str "int"
	| Real_t => str "real"
        | String_t => str "str"
        | Char_t => str "char"
        | Id_t id => str id
        | Tuple_t(ts) => (  str "(";
			    begin ();
                            sep pp (fn () => (str " * "; br ()))
                                   (List.map (fn (e) =>
                                                fn () => typ2s pp 0 senv e)
                                             ts);
                            stop ();
                            str ")" )
        | Record_t (ts) => ( str "{";
                            begin ();
                            sep pp (fn () => (str ","; br ()))
                                   (List.map (fn (id,typ) =>
                                                fn () => (str id; str ":"; typ2s pp 0 senv typ))
                                             ts);
                            stop ();
                            str ")" )
        | DataTyp_t s => str s
        | Ref_t typp => (str " ref "; typ2s pp 0 senv typp)
        | Fn_t (arg,res) => (begin ();
                              (str "(";
			       typ2s pp 0 senv arg; str " -> "; typ2s pp 0 senv res;
                               str ")";
                             stop ()))
        | Wrong_t => str "bad type"
    in
      if (p' > p) then s pp  else (str "("; s pp; str ")")
    end

    fun printType (typp:typ):string = 
  	 let
	    fun ppExp' (p:P.ppstream) (typp:typ):unit = typ2s p 0 [] typp;
	 in
	    P.pp_to_string 80 ppExp' typp
	 end
  end
