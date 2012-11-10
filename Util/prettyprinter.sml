
structure PrettyPrinter :> sig

    val ppExp: AbSyn.exp -> string
    val ppDecl: AbSyn.decl -> string
    val ppTyp : AbSyn.typ -> string

    val ppExpTyp : (AbSyn.exp * AbSyn.typ) -> string

end = struct

    open AbSyn
    structure P = PrettyPrint

    fun sep pp s l =
      case l of
        [] => ()
      | [x] => x ()
      | (x::xs) => (x (); s (); sep pp s xs)

    val max_prec = 999;

    fun binop_prec(b:binop):int =
        case b of
    	    Plus => 7
          | Times => 8
          | Minus => 7
          | Concat => 7
          | Equal => 5
          | GreaterThan => 5
          | LessThan => 5
          | GreaterThanEq => 5
          | LessThanEq => 5

    fun prec(e:exp):int =
        case e of
	    Const_e(c) => max_prec -1
          | Id_e(x) => max_prec
          | Fn_e(id,t,e) => 1
          | App_e(e1,e2) => 2
          | Unop_e (u,e) => 2
          | Binop_e(e1,b,e2) => binop_prec(b)
          | Tuple_e(es) => max_prec -1
          | Ith_e(i,e) => 2
          | Record_e(ides) => max_prec -1
          | Field_e(x,e,_) => 2
          | DataCon_e(x,NONE) => 2
          | DataCon_e(x,SOME(e)) => 2
          | Case_e(e,cases) => 1
          | Let_e(d,e) => max_prec -1
          | Deref_e _ => 2
          | Assign_e _ => 2
          | Ref_e _ => 2
          | Error_e(e)=> 2
          | If_e(e1,e2,e3) => 2

    fun const2s (c: const):string =
        case c of
    	    Int_c(i) => Int.toString i
          | Real_c(r) => Real.toString r
          | String_c(s) => concat ["\"",s,"\""]
          | Char_c(c) => concat ["#\"",Char.toString c, "\""]

    fun unop2s (u: unop):string =
      case u of
        Neg => "~"
      | Not => "not"
      | isNil => "isNil"
      | isSome => "isSome"
      | isTrue => "isTrue"
      | isFalse => "isFalse"
      | isCons => "isCons"
      | isNullary => "isNullary"
      | isValueCarry => "isValueCarry"
      | valueOf => "valueOf"
      | isNone => "isNone"

    fun binop2s (b: binop):string =
        case b of
	    Plus => "+"
          | Minus => "-"
          | Times => "*"
          | Concat => "^"
          | Equal => "="
          | GreaterThan => ">"
          | LessThan => "<"
          | GreaterThanEq => ">="
          | LessThanEq => "<="

    fun exp2s (pp:P.ppstream) (p:int) (e:exp):unit = let
      fun begin () = P.begin_block pp P.INCONSISTENT 0
      fun stop () = P.end_block pp
      fun brI () = P.add_break pp (1,2)
      fun br () = P.add_break pp (1,0)
      fun str (s) = P.add_string pp s
      val p' = prec(e)
      val e2s = exp2s pp p'
      fun case2s (p:pat,e:exp):unit = (begin ();
                                           pat2s pp p;
                                           str " =>";
                                           brI ();
                                           exp2s pp 0 e;
                                           stop ())
      fun s pp =
        case e of
          Const_e(c) => str (const2s c)
        | Id_e(x) => str (x)
        | Fn_e(id,t,e) => (begin ();
                             str "fn (";
                             str id;
                             str ":";
                             typ2s pp t;
                             str ")";
                             str " =>";
                             brI ();
                             e2s e;
                             stop ())
        | App_e(e1,e2) => (begin ();
                             e2s e1;
                             brI ();
                             e2s e2;
                             stop ())
        | Unop_e (u,e) => (begin ();
                             str (unop2s u);
                             brI ();
                             e2s e;
                             stop ())
        | Binop_e(e1,b,e2) => (begin ();
                                 e2s e1;
                                 str " ";
                                 str (binop2s b);
                                 brI ();
                                 e2s e2;
                                 stop ())
        | Tuple_e(es) => (str "(";
                            begin ();
                            sep pp (fn () => (str ",";
                                              br ()))
                                   (List.map (fn (e) =>
                                                fn () => exp2s pp 0 e)
                                             es);
                            stop ();
                            str ")")
        | Ith_e(i,e) => (begin ();
                           str "#";
                           str (Int.toString i);
                           str " ";
                           e2s e;
                           stop ())
        | Record_e(ides) => (str "{";
                               begin ();
                               sep pp (fn () => (str "," ;
                                                 br ()))
                                      (List.map  (fn (x,e) =>
                                                    (fn () => (str x;
                                                               str "=";
                                                               exp2s pp 0 e)))
                                                 ides);
                               stop ();
                               str "}")
        | Field_e(x,e,_) => (begin ();
                             str "#";
                             str x;
                             brI ();
                             e2s e;
                             stop ())
        | DataCon_e(x,NONE) => str x
        | DataCon_e(x,SOME(e)) => (begin ();
                                     str x;
                                     brI ();
                                     e2s e;
                                     stop ())
        | Case_e(e,cases) =>
            (begin ();
             str "case ";
             exp2s pp 0 e;
             str " of";
             brI ();
             begin ();
             sep pp (fn () => (br ();
                               str "| "))
                    (List.map (fn (c) => fn () => case2s c) cases);
             stop ();
             stop ())
        | Let_e(dl,e) =>
            (begin ();
             str "let";
             declList2s pp dl;
             str "in ";
             exp2s pp 0 e;
             str " end ";
             stop ())
        | If_e(e1,e2,e3) =>
            (begin ();
             str "if ";
             exp2s pp 0 e1;
             str " then ";
             brI ();
             begin ();
             exp2s pp 0 e2;
             stop ();
             str " else";
             brI ();
             begin ();
             exp2s pp 0 e3;
             stop())
        | Deref_e (e) => (begin ();
                          str "!";
                          e2s e;
                          stop ())
        | Assign_e (e1,e2) => (begin ();
                               e2s e1;
                               str " := ";
                               brI ();
                               e2s e2;
                               stop ())
        | Error_e (e) => (str "error(";
                          e2s e;
                          str ")")
        | Ref_e (e) => (str "ref ";
			e2s e)

    in
      if (p' > p) then s pp  else (str "("; s pp; str ")")
    end

    and declList2s (pp:P.ppstream) (dl: decl list):unit = let
      fun str (s) = P.add_string pp s
    in
      case dl of
	[] => str " "
      | d::t => (str " "; decl2s pp d; declList2s pp t)
    end

    and decl2s (pp:P.ppstream) (d: decl):unit =  let
      fun begin () = P.begin_block pp P.INCONSISTENT 0
      fun stop () = P.end_block pp
      fun brI () = P.add_break pp (1,2)
      fun br () = P.add_break pp (1,2)
      fun str (s) = P.add_string pp s
    in
       case d of
         Val_d(p, e) => (begin ();
                           str "val ";
                           pat2s pp p;
                           str " =";
                           brI ();
                           exp2s pp 0 e;
                           stop ())
       | Fun_d({name,arg,arg_typ,ret_typ}, e) =>
            (begin ();
             str "fun ";
             str name;
             str "(";
             str arg;
             str ":";
             typ2s pp arg_typ;
             str "):";
             typ2s pp ret_typ;
             str " =";
             brI ();
             exp2s pp 0 e;
             stop ())
    end

    and pat2s (pp:P.ppstream) (p:pat):unit = let
      fun begin () = P.begin_block pp P.INCONSISTENT 0
      fun stop () = P.end_block pp
      fun brI () = P.add_break pp (1,2)
      fun br () = P.add_break pp (1,2)
      fun str (s) = P.add_string pp s
    in
      case p of
        Wild_p => str "_"
      | Id_p(x) => str x
      | Const_p(i) => str (Int.toString i)
      | DataCon_p(id,NONE) => str (id)
      | DataCon_p(id,SOME(p)) => (str id;
                                    str " ";
                                    pat2s pp p)
      | Tuple_p(ps) => (str "(";
                          begin ();
                          sep pp (fn () => (str ",";
                                            br ()))
                              (List.map (fn p => fn () => pat2s pp p) ps);
                          stop ();
                          str ")")
      | Record_p(idps) =>
          (str "{";
           begin ();
           sep pp (fn () => (str ",";
                             br ()))
               (List.map (fn (x,p) => fn () => (str x;
                                                str "=";
                                                pat2s pp p)) idps);
           stop ();
           str "}")
    end

    and typ2s (pp:P.ppstream) (t: typ):unit = let
      fun begin () = P.begin_block pp P.INCONSISTENT 0
      fun stop () = P.end_block pp
      fun brI () = P.add_break pp (1,2)
      fun br () = P.add_break pp (1,2)
      fun str (s) = P.add_string pp s
    in
      case t of
        Int_t => str "int"
      | Real_t => str "real"
      | String_t => str "string"
      | Char_t => str "char"
      | Tuple_t([]) => str "unit"
      | Tuple_t(ts) => (str "(";
                          begin ();
                          sep pp (fn () => (str " *";
                                            br ()))
                              (List.map (fn t => fn () => typ2s pp t) ts);
                          stop ();
                          str ")")
      | Record_t(its) => (str "{";
                            begin ();
                            sep pp (fn () => (str ",";
                                              br ()))
                                (List.map (fn (a, b) =>
                                             fn () => (str a;
                                                       str ":";
                                                       typ2s pp b)) its);
                            stop ();
                            str "}")
      | DataTyp_t (id) => str id
      | Fn_t (t1,t2) => (begin ();
                           case t1 of
                             Fn_t _ => (str "("; typ2s pp t1; str ")")
                           | _ => typ2s pp t1;
                           str " ->";
                           brI ();
                           typ2s pp t2;
                           stop ())
      | Ref_t (t) => (typ2s pp t;
                        str " ref")
      | Id_t(name) => str name
    end

    fun ppExp (e:exp):string = let
      fun ppExp' (p:P.ppstream) (e:exp):unit = exp2s p 0 e;
    in
      P.pp_to_string 80 ppExp' e
    end

    fun ppDecl (d:decl):string = let
      fun ppDecl' (p:P.ppstream) (d:decl):unit = decl2s p d
    in
      P.pp_to_string 80 decl2s d
    end

    fun ppTyp (t:typ):string = let
      fun ppTyp' (p:P.ppstream) (t:typ):unit = typ2s p t
    in
      P.pp_to_string 80 typ2s t
    end

    fun ppExpTyp (e:exp,t:typ):string = let
      fun ppExpTyp' (p:P.ppstream) (e:exp,t:typ):unit =
        (P.begin_block p P.INCONSISTENT 0;
         exp2s p 0 e;
         P.add_break p (1,1);
         P.add_string p ": ";
         typ2s p t;
         P.end_block p)
    in
      P.pp_to_string 80 ppExpTyp' (e,t)
    end

end

