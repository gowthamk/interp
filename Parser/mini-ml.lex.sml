functor MiniMLLexFun(structure Tokens: MiniML_TOKENS
                              structure D :DATA_TYPES)=
   struct
    structure UserDeclarations =
      struct

structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

structure A = Atom

structure Keywords =
    struct
        type pos = int
        type token = (svalue, pos) Tokens.token

        val atomTrue = A.atom "true"
        val atomFalse = A.atom "false"

        fun ident (a,p1,p2) =
          if A.sameAtom (a,atomTrue)
            then Tokens.DATACON ("true",p1,p2)
          else if A.sameAtom (a,atomFalse)
            then Tokens.DATACON ("false",p1,p2)
          else
            Tokens.ID (Atom.toString (a),p1,p2)
        fun mkKW (kw,tk) = (kw, fn (p1:pos,p2:pos) => tk (p1,p2))

        val keywords = map mkKW
          [("int", Tokens.KW_int),
           ("real", Tokens.KW_real),
           ("string",Tokens.KW_string),
           ("char",Tokens.KW_char),
           ("fn",Tokens.KW_fn),
           ("case",Tokens.KW_case),
           ("of",Tokens.KW_of),
           ("let",Tokens.KW_let),
           ("in",Tokens.KW_in),
           ("end",Tokens.KW_end),
           ("val",Tokens.KW_val),
           ("fun",Tokens.KW_fun),
           ("ref",Tokens.KW_ref),
           ("not",Tokens.KW_not),
           ("if", Tokens.KW_if),
           ("then", Tokens.KW_then),
           ("else", Tokens.KW_else),
           ("unit", Tokens.KW_unit),
	   ("error",Tokens.KW_error)
          ]
    end

structure K = KeywordFn (Keywords)

(* line number *)
val pos = ref 1
fun error (e,l : int,_) =
     (TextIO.output (TextIO.stdOut,
                     String.concat["line ", (Int.toString l), ": ", e, "\n"]);
      raise Fail "")
fun eof () = Tokens.EOF(!pos,!pos)

val charlist = ref ([] : string list)

val commentNesting = ref (0)

fun addString (s) = (charlist :=  s::(!charlist))
fun makeString () = (concat(rev(!charlist)) before charlist:=[])

fun recognizeDataCon (id,p1,p2) =
  case D.isNullCons (id) of
    NONE => K.keyword(id,p1,p2)
  | SOME (b) => if (b)
                  then Tokens.DATACON (id,p1,p2)
                else Tokens.DATACONARG (id,p1,p2)


end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [ 
 (0, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1, 
"\009\009\009\009\009\009\009\009\009\050\054\009\009\052\009\009\
\\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\009\
\\050\049\048\046\009\009\009\009\044\043\042\041\040\038\037\009\
\\036\036\036\036\036\036\036\036\036\036\034\033\031\029\027\023\
\\009\021\021\021\021\021\021\021\021\021\021\021\021\021\021\021\
\\021\021\021\021\021\021\021\021\021\021\021\009\009\009\020\019\
\\009\017\017\017\017\017\017\017\017\017\017\017\017\017\017\017\
\\017\017\017\017\017\017\017\017\017\017\017\016\015\014\010\009\
\\009"
),
 (3, 
"\055\055\055\055\055\055\055\055\055\055\060\055\055\059\055\055\
\\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\
\\055\055\058\055\055\055\055\055\055\055\055\055\055\055\055\055\
\\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\
\\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\
\\055\055\055\055\055\055\055\055\055\055\055\055\056\055\055\055\
\\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\
\\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\055\
\\055"
),
 (5, 
"\061\061\061\061\061\061\061\061\061\061\066\061\061\065\061\061\
\\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\
\\061\061\064\061\061\061\061\061\061\061\061\061\061\061\061\061\
\\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\
\\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\
\\061\061\061\061\061\061\061\061\061\061\061\061\062\061\061\061\
\\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\
\\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\061\
\\061"
),
 (7, 
"\067\067\067\067\067\067\067\067\067\067\000\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\070\067\068\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\
\\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\067\
\\067"
),
 (10, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\012\000\
\\011\011\011\011\011\011\011\011\011\011\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (12, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\013\013\013\013\013\013\013\013\013\013\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (17, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\018\000\000\000\000\000\000\000\000\
\\018\018\018\018\018\018\018\018\018\018\000\000\000\000\000\000\
\\000\018\018\018\018\018\018\018\018\018\018\018\018\018\018\018\
\\018\018\018\018\018\018\018\018\018\018\018\000\000\000\000\018\
\\000\018\018\018\018\018\018\018\018\018\018\018\018\018\018\018\
\\018\018\018\018\018\018\018\018\018\018\018\000\000\000\000\000\
\\000"
),
 (21, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\000\
\\022\022\022\022\022\022\022\022\022\022\000\000\000\000\000\000\
\\000\022\022\022\022\022\022\022\022\022\022\022\022\022\022\022\
\\022\022\022\022\022\022\022\022\022\022\022\000\000\000\000\022\
\\000\022\022\022\022\022\022\022\022\022\022\022\022\022\022\022\
\\022\022\022\022\022\022\022\022\022\022\022\000\000\000\000\000\
\\000"
),
 (23, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\024\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (24, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\026\000\025\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (27, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\028\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (29, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\030\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (31, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\032\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (34, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\035\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (38, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\039\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (44, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\045\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (46, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\047\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (50, 
"\000\000\000\000\000\000\000\000\000\051\051\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\051\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (52, 
"\000\000\000\000\000\000\000\000\000\000\053\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (56, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\057\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (59, 
"\000\000\000\000\000\000\000\000\000\000\060\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (62, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\063\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (65, 
"\000\000\000\000\000\000\000\000\000\000\066\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (68, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\069\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (70, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\071\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
(0, "")]
fun f x = x 
val s = map f (rev (tl (rev s))) 
exception LexHackingError 
fun look ((j,x)::r, i: int) = if i = j then x else look(r, i) 
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)} 
in Vector.fromList(map g 
[{fin = [], trans = 0},
{fin = [], trans = 1},
{fin = [], trans = 1},
{fin = [], trans = 3},
{fin = [], trans = 3},
{fin = [], trans = 5},
{fin = [], trans = 5},
{fin = [], trans = 7},
{fin = [], trans = 7},
{fin = [(N 133)], trans = 0},
{fin = [(N 115),(N 133)], trans = 10},
{fin = [(N 36)], trans = 10},
{fin = [], trans = 12},
{fin = [(N 42)], trans = 12},
{fin = [(N 32),(N 133)], trans = 0},
{fin = [(N 89),(N 133)], trans = 0},
{fin = [(N 27),(N 133)], trans = 0},
{fin = [(N 22),(N 133)], trans = 17},
{fin = [(N 22)], trans = 17},
{fin = [(N 22),(N 63),(N 133)], trans = 17},
{fin = [(N 117),(N 133)], trans = 0},
{fin = [(N 14),(N 22),(N 133)], trans = 21},
{fin = [(N 14),(N 22)], trans = 21},
{fin = [(N 133)], trans = 23},
{fin = [], trans = 24},
{fin = [(N 32)], trans = 0},
{fin = [(N 27)], trans = 0},
{fin = [(N 105),(N 133)], trans = 27},
{fin = [(N 108)], trans = 0},
{fin = [(N 103),(N 133)], trans = 29},
{fin = [(N 101)], trans = 0},
{fin = [(N 110),(N 133)], trans = 31},
{fin = [(N 113)], trans = 0},
{fin = [(N 61),(N 133)], trans = 0},
{fin = [(N 70),(N 133)], trans = 34},
{fin = [(N 68)], trans = 0},
{fin = [(N 36),(N 133)], trans = 10},
{fin = [(N 133)], trans = 12},
{fin = [(N 98),(N 133)], trans = 38},
{fin = [(N 96)], trans = 0},
{fin = [(N 65),(N 133)], trans = 0},
{fin = [(N 93),(N 133)], trans = 0},
{fin = [(N 91),(N 133)], trans = 0},
{fin = [(N 87),(N 133)], trans = 0},
{fin = [(N 85),(N 133)], trans = 44},
{fin = [(N 75)], trans = 0},
{fin = [(N 59),(N 133)], trans = 46},
{fin = [(N 45)], trans = 0},
{fin = [(N 119),(N 133)], trans = 0},
{fin = [(N 72),(N 133)], trans = 0},
{fin = [(N 7),(N 133)], trans = 50},
{fin = [(N 7)], trans = 50},
{fin = [(N 4),(N 133)], trans = 52},
{fin = [(N 4)], trans = 0},
{fin = [(N 4),(N 7)], trans = 50},
{fin = [(N 131),(N 133)], trans = 0},
{fin = [(N 131),(N 133)], trans = 56},
{fin = [(N 129)], trans = 0},
{fin = [(N 126),(N 131),(N 133)], trans = 0},
{fin = [(N 124),(N 131),(N 133)], trans = 59},
{fin = [(N 124)], trans = 0},
{fin = [(N 57),(N 133)], trans = 0},
{fin = [(N 57),(N 133)], trans = 62},
{fin = [(N 55)], trans = 0},
{fin = [(N 52),(N 57),(N 133)], trans = 0},
{fin = [(N 50),(N 57),(N 133)], trans = 65},
{fin = [(N 50)], trans = 0},
{fin = [(N 83),(N 133)], trans = 0},
{fin = [(N 83),(N 133)], trans = 68},
{fin = [(N 78)], trans = 0},
{fin = [(N 83),(N 133)], trans = 70},
{fin = [(N 81)], trans = 0}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val CHAR = STARTSTATE 5;
val COMMENT = STARTSTATE 7;
val INITIAL = STARTSTATE 1;
val STRING = STARTSTATE 3;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

fun makeLexer yyinput =
let	val yygone0=1
	val yyb = ref "\n" 		(* buffer *)
	val yybl = ref 1		(*buffer length *)
	val yybufpos = ref 1		(* location of next character to use *)
	val yygone = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex () : Internal.result =
let fun continue() = lex() in
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0) =
	let fun action (i,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let fun yymktext() = substring(!yyb,i0,i-i0)
			     val yypos = i0+ !yygone
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  101 => (Tokens.DARROW(!pos,!pos))
| 103 => (Tokens.EQSIGN(!pos,!pos))
| 105 => (Tokens.GREATER(!pos,!pos))
| 108 => (Tokens.GREATEREQ(!pos, !pos))
| 110 => (Tokens.LESS(!pos,!pos))
| 113 => (Tokens.LESSEQ(!pos, !pos))
| 115 => (Tokens.NEG(!pos,!pos))
| 117 => (Tokens.CARET(!pos,!pos))
| 119 => (YYBEGIN STRING; charlist := [""]; continue ())
| 124 => (YYBEGIN INITIAL;
                  error ("unterminated string constant",!pos,!pos);
                  pos := (!pos)+1; (* charlist := "";*)
                  continue() )
| 126 => (YYBEGIN INITIAL;
               Tokens.STRING (makeString (), !pos,!pos))
| 129 => (addString "\""; continue())
| 131 => let val yytext=yymktext() in addString (yytext); continue () end
| 133 => let val yytext=yymktext() in error ("bad character "^yytext,!pos,!pos);
                 continue() end
| 14 => let val yytext=yymktext() in recognizeDataCon (yytext,!pos,!pos) end
| 22 => let val yytext=yymktext() in K.keyword (yytext,!pos,!pos) end
| 27 => (Tokens.LBRACE(!pos,!pos))
| 32 => (Tokens.RBRACE(!pos,!pos))
| 36 => let val yytext=yymktext() in Tokens.INT(valOf (Int.fromString (yytext)),!pos,!pos) end
| 4 => (pos := (!pos) + 1; continue())
| 42 => let val yytext=yymktext() in Tokens.REAL(valOf (Real.fromString (yytext)),!pos,!pos) end
| 45 => (YYBEGIN CHAR; charlist:=[""];continue ())
| 50 => (YYBEGIN INITIAL;
                error ("unterminated character constant",!pos,!pos);
                pos := (!pos)+1;
                continue ())
| 52 => (YYBEGIN INITIAL;
             (*if length(!charlist)=2 then*)
             let val c = makeString()
             in
               if String.size(c) = 1 then
                   Tokens.CHAR (valOf (Char.fromString (c)),!pos,!pos)
               else error("invalid character", !pos, !pos)
             end)
| 55 => (addString "\""; continue() )
| 57 => let val yytext=yymktext() in addString (yytext); continue () end
| 59 => (Tokens.HASH(!pos,!pos))
| 61 => (Tokens.SEMICOLON(!pos,!pos))
| 63 => (Tokens.UNDERSCORE(!pos,!pos))
| 65 => (Tokens.COMMA(!pos,!pos))
| 68 => (Tokens.ASSGN(!pos,!pos))
| 7 => (continue())
| 70 => (Tokens.COLON(!pos,!pos))
| 72 => (Tokens.BANG (!pos,!pos))
| 75 => (YYBEGIN COMMENT; commentNesting := 0; continue ())
| 78 => (if (!commentNesting)=0
                    then (YYBEGIN INITIAL;
                          continue ())
                  else (commentNesting := (!commentNesting)-1;
                        continue ()))
| 81 => (commentNesting := (!commentNesting)+1;
                  continue ())
| 83 => (continue())
| 85 => (Tokens.LPAREN(!pos,!pos))
| 87 => (Tokens.RPAREN(!pos,!pos))
| 89 => (Tokens.BAR(!pos,!pos))
| 91 => (Tokens.TIMES(!pos,!pos))
| 93 => (Tokens.PLUS(!pos,!pos))
| 96 => (Tokens.ARROW(!pos,!pos))
| 98 => (Tokens.MINUS(!pos,!pos))
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Unsafe.Vector.sub(Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof ()
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord(Unsafe.CharVector.sub(!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord(Unsafe.CharVector.sub(trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
end
  in lex
  end
end
