signature MiniML_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val SEMICOLON:  'a * 'a -> (svalue,'a) token
val NEG:  'a * 'a -> (svalue,'a) token
val GREATEREQ:  'a * 'a -> (svalue,'a) token
val GREATER:  'a * 'a -> (svalue,'a) token
val LESSEQ:  'a * 'a -> (svalue,'a) token
val LESS:  'a * 'a -> (svalue,'a) token
val STRING: (string) *  'a * 'a -> (svalue,'a) token
val ASSGN:  'a * 'a -> (svalue,'a) token
val BANG:  'a * 'a -> (svalue,'a) token
val EQSIGN:  'a * 'a -> (svalue,'a) token
val CARET:  'a * 'a -> (svalue,'a) token
val DARROW:  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val MINUS:  'a * 'a -> (svalue,'a) token
val PLUS:  'a * 'a -> (svalue,'a) token
val TIMES:  'a * 'a -> (svalue,'a) token
val BAR:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val COLON:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val UNDERSCORE:  'a * 'a -> (svalue,'a) token
val HASH:  'a * 'a -> (svalue,'a) token
val CHAR: (char) *  'a * 'a -> (svalue,'a) token
val REAL: (real) *  'a * 'a -> (svalue,'a) token
val INT: (int) *  'a * 'a -> (svalue,'a) token
val RBRACE:  'a * 'a -> (svalue,'a) token
val LBRACE:  'a * 'a -> (svalue,'a) token
val DATACONARG: (string) *  'a * 'a -> (svalue,'a) token
val DATACON: (string) *  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val KW_error:  'a * 'a -> (svalue,'a) token
val KW_unit:  'a * 'a -> (svalue,'a) token
val KW_else:  'a * 'a -> (svalue,'a) token
val KW_then:  'a * 'a -> (svalue,'a) token
val KW_if:  'a * 'a -> (svalue,'a) token
val KW_not:  'a * 'a -> (svalue,'a) token
val KW_ref:  'a * 'a -> (svalue,'a) token
val KW_fun:  'a * 'a -> (svalue,'a) token
val KW_val:  'a * 'a -> (svalue,'a) token
val KW_end:  'a * 'a -> (svalue,'a) token
val KW_in:  'a * 'a -> (svalue,'a) token
val KW_let:  'a * 'a -> (svalue,'a) token
val KW_of:  'a * 'a -> (svalue,'a) token
val KW_case:  'a * 'a -> (svalue,'a) token
val KW_fn:  'a * 'a -> (svalue,'a) token
val KW_char:  'a * 'a -> (svalue,'a) token
val KW_string:  'a * 'a -> (svalue,'a) token
val KW_real:  'a * 'a -> (svalue,'a) token
val KW_int:  'a * 'a -> (svalue,'a) token
end
signature MiniML_LRVALS=
sig
structure Tokens : MiniML_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
