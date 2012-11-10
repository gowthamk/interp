
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


%%
%s STRING CHAR COMMENT;
%header (functor MiniMLLexFun(structure Tokens: MiniML_TOKENS
                              structure D :DATA_TYPES));
eol=("\n"|"\013\n"|"\013");
alpha=[A-Za-z]|"_";
caps=[A-Z];
digit=[0-9];
hexdigit=[0-9a-fA-F];
ws=[\ \t \n];
allchar=({alpha}|{digit}|"_"|"'");
identifier={alpha}{allchar}*;
datacon={caps}{allchar}*;
lbrace=("\{"|"\?\?\<");
rbrace=("\}"|"\?\?\>");
integer="~"?{digit}+;
real="~"?{digit}*"."{digit}+;
text=({allchar} |{ws}|"+"|"!"|"~"|":"|"."|","|"("|")"|"*"|"="|{lbrace}|{rbrace});
%%
<INITIAL>{eol}    => (pos := (!pos) + 1; continue());
<INITIAL>{ws}+    => (continue());
<INITIAL>{datacon} => (recognizeDataCon (yytext,!pos,!pos));
<INITIAL>{identifier} => (K.keyword (yytext,!pos,!pos));
<INITIAL>{lbrace} => (Tokens.LBRACE(!pos,!pos));
<INITIAL>{rbrace} => (Tokens.RBRACE(!pos,!pos));
<INITIAL>{integer} => (Tokens.INT(valOf (Int.fromString (yytext)),!pos,!pos));
<INITIAL>{real} => (Tokens.REAL(valOf (Real.fromString (yytext)),!pos,!pos));
<INITIAL>"#"\" => (YYBEGIN CHAR; charlist:=[""];continue ());
<CHAR>{eol} => (YYBEGIN INITIAL;
                error ("unterminated character constant",!pos,!pos);
                pos := (!pos)+1;
                continue ());
<CHAR>\" => (YYBEGIN INITIAL;
             (*if length(!charlist)=2 then*)
             let val c = makeString()
             in
               if String.size(c) = 1 then
                   Tokens.CHAR (valOf (Char.fromString (c)),!pos,!pos)
               else error("invalid character", !pos, !pos)
             end);
<CHAR>"\\\"" => (addString "\""; continue() );
<CHAR>. => (addString (yytext); continue ());
<INITIAL>"#" => (Tokens.HASH(!pos,!pos));
<INITIAL>";" => (Tokens.SEMICOLON(!pos,!pos));
<INITIAL>"_" => (Tokens.UNDERSCORE(!pos,!pos));
<INITIAL>"," => (Tokens.COMMA(!pos,!pos));
<INITIAL>":=" => (Tokens.ASSGN(!pos,!pos));
<INITIAL>":" => (Tokens.COLON(!pos,!pos));
<INITIAL>"!" => (Tokens.BANG (!pos,!pos));
<INITIAL>"(*" => (YYBEGIN COMMENT; commentNesting := 0; continue ());
<COMMENT>"*)" => (if (!commentNesting)=0
                    then (YYBEGIN INITIAL;
                          continue ())
                  else (commentNesting := (!commentNesting)-1;
                        continue ()));
<COMMENT>"(*" => (commentNesting := (!commentNesting)+1;
                  continue ());
<COMMENT>. => (continue());
<INITIAL>"(" => (Tokens.LPAREN(!pos,!pos));
<INITIAL>")" => (Tokens.RPAREN(!pos,!pos));
<INITIAL>"|" => (Tokens.BAR(!pos,!pos));
<INITIAL>"*" => (Tokens.TIMES(!pos,!pos));
<INITIAL>"+" => (Tokens.PLUS(!pos,!pos));
<INITIAL>"->" => (Tokens.ARROW(!pos,!pos));
<INITIAL>"-" => (Tokens.MINUS(!pos,!pos));
<INITIAL>"=>" => (Tokens.DARROW(!pos,!pos));
<INITIAL>"=" => (Tokens.EQSIGN(!pos,!pos));
<INITIAL>">" => (Tokens.GREATER(!pos,!pos));
<INITIAL>">=" => (Tokens.GREATEREQ(!pos, !pos));
<INITIAL>"<" => (Tokens.LESS(!pos,!pos));
<INITIAL>"<=" => (Tokens.LESSEQ(!pos, !pos));
<INITIAL>"~" => (Tokens.NEG(!pos,!pos));
<INITIAL>"^" => (Tokens.CARET(!pos,!pos));

<INITIAL>\" => (YYBEGIN STRING; charlist := [""]; continue ());
<STRING>{eol} => (YYBEGIN INITIAL;
                  error ("unterminated string constant",!pos,!pos);
                  pos := (!pos)+1; (* charlist := "";*)
                  continue() );


<STRING>\" => (YYBEGIN INITIAL;
               Tokens.STRING (makeString (), !pos,!pos));
<STRING>"\\\"" => (addString "\""; continue());
<STRING>. => (addString (yytext); continue ());
.            => (error ("bad character "^yytext,!pos,!pos);
                 continue());
