
structure Parser : sig
  val parse : TextIO.instream -> AbSyn.top_level option
  val parseString : string -> AbSyn.top_level option
end = struct


  (* There is a lot of stuff here that is boilerplate and hard to
   * explain. You don't need to worry about this code
   *)

  structure MiniMLLrVals = MiniMLLrValsFun(structure Token = LrParser.Token)
  structure MiniMLLex = MiniMLLexFun(structure Tokens = MiniMLLrVals.Tokens
                                     structure D = DataTypes)
  structure MiniMLParser = Join (structure LrParser = LrParser
                                 structure ParserData = MiniMLLrVals.ParserData
                                 structure Lex = MiniMLLex)

  fun invoke (lexstream) = let
    val print_error = fn (s,i:int,_) =>
      Error.parse (concat [s," [line ",(Int.toString i),"]"])
  in
    MiniMLParser.parse(0,lexstream,print_error,())
  end

  fun parse (instream) = let
    val lexer = MiniMLParser.makeLexer (fn _ => (case (TextIO.inputLine instream) of
                                                   NONE => ""
                                                 | SOME s => s))
    val dummyEOF = MiniMLLrVals.Tokens.EOF(0,0)
    fun loop lexer = let
      val (result,lexer) = invoke lexer
      val (nextToken,lexer) = MiniMLParser.Stream.get lexer
    in if MiniMLParser.sameToken(nextToken,dummyEOF) then result
       else loop lexer
    end
  in
    MiniMLLex.UserDeclarations.pos := 1;
    Option.join (SOME (loop lexer) handle _ => NONE)
  end

  fun parseString (string) = let
    val s = TextIO.openString (string)
    val r = parse (s)
  in
    TextIO.closeIn (s);
    r
  end

end
