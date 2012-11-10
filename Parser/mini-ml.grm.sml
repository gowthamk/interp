functor MiniMLLrValsFun (structure Token : TOKEN) : MiniML_LRVALS = 
struct
structure ParserData=
struct
structure Header = 
struct

open AbSyn

val c = Unsafe.cast (0)


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\142\000\002\000\141\000\003\000\140\000\004\000\139\000\
\\018\000\138\000\020\000\137\000\023\000\136\000\032\000\135\000\000\000\
\\001\000\005\000\033\000\006\000\032\000\008\000\031\000\013\000\028\000\
\\014\000\027\000\015\000\026\000\019\000\025\000\020\000\024\000\
\\021\000\023\000\022\000\022\000\023\000\021\000\025\000\020\000\
\\026\000\019\000\027\000\018\000\028\000\017\000\032\000\016\000\
\\033\000\053\000\042\000\015\000\044\000\014\000\049\000\013\000\000\000\
\\001\000\005\000\033\000\006\000\032\000\008\000\031\000\013\000\028\000\
\\014\000\027\000\015\000\026\000\019\000\025\000\020\000\024\000\
\\021\000\023\000\022\000\022\000\023\000\021\000\025\000\020\000\
\\026\000\019\000\027\000\018\000\028\000\017\000\032\000\016\000\
\\042\000\015\000\044\000\014\000\049\000\013\000\000\000\
\\001\000\007\000\101\000\000\000\
\\001\000\008\000\031\000\013\000\028\000\014\000\027\000\019\000\025\000\
\\020\000\024\000\021\000\023\000\023\000\021\000\025\000\020\000\
\\026\000\019\000\027\000\018\000\032\000\016\000\042\000\015\000\
\\044\000\014\000\049\000\013\000\000\000\
\\001\000\009\000\100\000\000\000\
\\001\000\010\000\130\000\000\000\
\\001\000\013\000\155\000\033\000\154\000\038\000\153\000\000\000\
\\001\000\013\000\155\000\033\000\161\000\038\000\153\000\000\000\
\\001\000\013\000\155\000\033\000\166\000\035\000\165\000\038\000\153\000\000\000\
\\001\000\013\000\155\000\038\000\153\000\041\000\160\000\000\000\
\\001\000\013\000\155\000\038\000\153\000\041\000\184\000\000\000\
\\001\000\016\000\092\000\000\000\
\\001\000\017\000\125\000\000\000\
\\001\000\020\000\055\000\025\000\054\000\000\000\
\\001\000\020\000\057\000\000\000\
\\001\000\020\000\063\000\000\000\
\\001\000\020\000\071\000\021\000\070\000\022\000\069\000\023\000\068\000\
\\025\000\067\000\029\000\066\000\032\000\065\000\000\000\
\\001\000\020\000\098\000\000\000\
\\001\000\020\000\103\000\033\000\102\000\000\000\
\\001\000\020\000\109\000\033\000\108\000\000\000\
\\001\000\020\000\144\000\000\000\
\\001\000\020\000\158\000\000\000\
\\001\000\020\000\162\000\000\000\
\\001\000\020\000\187\000\000\000\
\\001\000\024\000\090\000\000\000\
\\001\000\024\000\114\000\000\000\
\\001\000\024\000\167\000\000\000\
\\001\000\030\000\087\000\033\000\086\000\000\000\
\\001\000\031\000\121\000\000\000\
\\001\000\031\000\126\000\000\000\
\\001\000\031\000\127\000\000\000\
\\001\000\031\000\168\000\000\000\
\\001\000\031\000\171\000\000\000\
\\001\000\031\000\189\000\000\000\
\\001\000\032\000\074\000\000\000\
\\001\000\032\000\093\000\000\000\
\\001\000\033\000\085\000\000\000\
\\001\000\033\000\111\000\000\000\
\\001\000\033\000\180\000\000\000\
\\001\000\039\000\120\000\000\000\
\\001\000\039\000\131\000\000\000\
\\001\000\039\000\164\000\000\000\
\\001\000\041\000\091\000\000\000\
\\001\000\041\000\094\000\000\000\
\\001\000\041\000\115\000\000\000\
\\001\000\041\000\159\000\000\000\
\\001\000\041\000\172\000\000\000\
\\001\000\051\000\000\000\000\000\
\\193\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\050\000\046\000\000\000\
\\197\000\000\000\
\\198\000\000\000\
\\199\000\000\000\
\\200\000\000\000\
\\201\000\000\000\
\\202\000\000\000\
\\203\000\000\000\
\\204\000\013\000\155\000\038\000\153\000\000\000\
\\205\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\\209\000\013\000\155\000\035\000\181\000\038\000\153\000\000\000\
\\210\000\000\000\
\\211\000\000\000\
\\212\000\013\000\155\000\030\000\183\000\038\000\153\000\000\000\
\\213\000\000\000\
\\214\000\000\000\
\\215\000\000\000\
\\216\000\000\000\
\\217\000\035\000\044\000\043\000\039\000\000\000\
\\218\000\035\000\044\000\043\000\039\000\000\000\
\\219\000\043\000\039\000\000\000\
\\220\000\035\000\044\000\036\000\043\000\037\000\042\000\040\000\041\000\
\\043\000\039\000\000\000\
\\221\000\035\000\044\000\043\000\039\000\000\000\
\\222\000\035\000\044\000\036\000\043\000\037\000\042\000\040\000\041\000\
\\043\000\039\000\000\000\
\\223\000\035\000\044\000\036\000\043\000\037\000\042\000\040\000\041\000\
\\043\000\039\000\000\000\
\\224\000\035\000\044\000\036\000\043\000\037\000\042\000\040\000\041\000\
\\043\000\039\000\000\000\
\\225\000\035\000\044\000\036\000\043\000\037\000\042\000\040\000\041\000\
\\043\000\039\000\000\000\
\\226\000\043\000\039\000\000\000\
\\227\000\000\000\
\\228\000\000\000\
\\229\000\000\000\
\\230\000\000\000\
\\231\000\000\000\
\\232\000\000\000\
\\233\000\000\000\
\\234\000\000\000\
\\235\000\000\000\
\\236\000\000\000\
\\237\000\000\000\
\\238\000\000\000\
\\239\000\000\000\
\\240\000\000\000\
\\241\000\000\000\
\\242\000\000\000\
\\243\000\000\000\
\\244\000\008\000\031\000\013\000\028\000\014\000\027\000\019\000\025\000\
\\020\000\024\000\021\000\023\000\023\000\021\000\025\000\020\000\
\\026\000\019\000\027\000\018\000\032\000\016\000\042\000\015\000\
\\044\000\014\000\049\000\013\000\000\000\
\\245\000\000\000\
\\246\000\035\000\044\000\036\000\043\000\037\000\042\000\040\000\041\000\
\\041\000\040\000\043\000\039\000\045\000\038\000\046\000\037\000\
\\047\000\036\000\048\000\035\000\000\000\
\\247\000\000\000\
\\248\000\000\000\
\\249\000\000\000\
\\250\000\000\000\
\\251\000\000\000\
\\252\000\000\000\
\\253\000\000\000\
\\254\000\000\000\
\\255\000\030\000\122\000\000\000\
\\000\001\000\000\
\\001\001\000\000\
\\002\001\000\000\
\\003\001\030\000\124\000\000\000\
\\004\001\000\000\
\\005\001\034\000\132\000\000\000\
\\006\001\000\000\
\\007\001\000\000\
\\008\001\000\000\
\\009\001\000\000\
\\010\001\000\000\
\\011\001\005\000\033\000\006\000\032\000\008\000\031\000\011\000\030\000\
\\012\000\029\000\013\000\028\000\014\000\027\000\015\000\026\000\
\\019\000\025\000\020\000\024\000\021\000\023\000\022\000\022\000\
\\023\000\021\000\025\000\020\000\026\000\019\000\027\000\018\000\
\\028\000\017\000\032\000\016\000\042\000\015\000\044\000\014\000\
\\049\000\013\000\000\000\
\\011\001\011\000\030\000\012\000\029\000\000\000\
\\012\001\000\000\
\\013\001\000\000\
\\014\001\000\000\
\\015\001\000\000\
\\016\001\000\000\
\\017\001\000\000\
\\018\001\000\000\
\\019\001\000\000\
\\020\001\000\000\
\\021\001\030\000\113\000\000\000\
\\022\001\000\000\
\\023\001\000\000\
\\024\001\030\000\150\000\000\000\
\"
val actionRowNumbers =
"\123\000\100\000\099\000\102\000\
\\052\000\124\000\052\000\090\000\
\\097\000\101\000\089\000\004\000\
\\071\000\004\000\001\000\014\000\
\\072\000\070\000\069\000\015\000\
\\002\000\096\000\088\000\004\000\
\\002\000\004\000\004\000\016\000\
\\017\000\124\000\002\000\035\000\
\\098\000\004\000\004\000\004\000\
\\004\000\004\000\004\000\004\000\
\\004\000\004\000\004\000\050\000\
\\051\000\122\000\049\000\084\000\
\\087\000\037\000\028\000\093\000\
\\002\000\002\000\025\000\043\000\
\\109\000\086\000\012\000\083\000\
\\085\000\036\000\044\000\017\000\
\\125\000\127\000\018\000\017\000\
\\129\000\126\000\005\000\003\000\
\\019\000\081\000\080\000\079\000\
\\078\000\082\000\076\000\077\000\
\\074\000\073\000\075\000\094\000\
\\092\000\002\000\103\000\104\000\
\\095\000\002\000\002\000\020\000\
\\002\000\038\000\134\000\026\000\
\\045\000\128\000\002\000\017\000\
\\040\000\029\000\112\000\111\000\
\\115\000\013\000\030\000\031\000\
\\119\000\130\000\132\000\017\000\
\\131\000\017\000\006\000\041\000\
\\117\000\106\000\002\000\000\000\
\\002\000\113\000\021\000\002\000\
\\000\000\000\000\134\000\137\000\
\\091\000\002\000\017\000\108\000\
\\007\000\000\000\022\000\059\000\
\\057\000\056\000\055\000\054\000\
\\053\000\110\000\046\000\105\000\
\\010\000\008\000\133\000\135\000\
\\023\000\118\000\116\000\000\000\
\\042\000\058\000\009\000\027\000\
\\032\000\002\000\002\000\033\000\
\\047\000\060\000\002\000\000\000\
\\063\000\062\000\000\000\115\000\
\\121\000\000\000\017\000\107\000\
\\039\000\065\000\068\000\114\000\
\\011\000\137\000\061\000\000\000\
\\066\000\024\000\002\000\136\000\
\\064\000\034\000\120\000\000\000\
\\068\000\067\000\048\000"
val gotoT =
"\
\\001\000\190\000\008\000\010\000\009\000\009\000\010\000\008\000\
\\011\000\007\000\013\000\006\000\020\000\005\000\021\000\004\000\
\\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\010\000\008\000\011\000\007\000\028\000\032\000\000\000\
\\000\000\
\\000\000\
\\002\000\043\000\000\000\
\\020\000\005\000\021\000\045\000\000\000\
\\002\000\046\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\010\000\008\000\011\000\007\000\028\000\047\000\000\000\
\\000\000\
\\008\000\010\000\010\000\008\000\011\000\007\000\028\000\048\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\050\000\015\000\049\000\027\000\003\000\028\000\002\000\
\\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\016\000\054\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\056\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\010\000\008\000\011\000\007\000\028\000\057\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\058\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\010\000\008\000\011\000\007\000\028\000\059\000\000\000\
\\008\000\010\000\010\000\008\000\011\000\007\000\028\000\060\000\000\000\
\\000\000\
\\022\000\062\000\000\000\
\\020\000\005\000\021\000\070\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\071\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\073\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\074\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\075\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\076\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\077\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\078\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\079\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\080\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\081\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\027\000\082\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\086\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\087\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\094\000\023\000\093\000\000\000\
\\000\000\
\\000\000\
\\025\000\095\000\000\000\
\\022\000\097\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\103\000\014\000\102\000\027\000\003\000\028\000\002\000\
\\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\104\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\105\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\108\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\024\000\110\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\114\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\018\000\117\000\019\000\116\000\022\000\115\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\017\000\121\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\022\000\126\000\000\000\
\\000\000\
\\022\000\127\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\131\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\003\000\132\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\103\000\014\000\141\000\027\000\003\000\028\000\002\000\
\\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\143\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\003\000\144\000\000\000\
\\003\000\145\000\000\000\
\\024\000\146\000\000\000\
\\026\000\147\000\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\149\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\018\000\150\000\019\000\116\000\022\000\115\000\000\000\
\\000\000\
\\000\000\
\\003\000\154\000\000\000\
\\006\000\155\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\161\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\167\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\168\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\171\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\003\000\173\000\004\000\172\000\000\000\
\\000\000\
\\000\000\
\\003\000\174\000\000\000\
\\017\000\175\000\000\000\
\\000\000\
\\003\000\176\000\000\000\
\\022\000\177\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\007\000\180\000\000\000\
\\000\000\
\\000\000\
\\026\000\183\000\000\000\
\\000\000\
\\003\000\173\000\004\000\184\000\000\000\
\\000\000\
\\000\000\
\\008\000\010\000\009\000\009\000\010\000\008\000\011\000\007\000\
\\013\000\186\000\027\000\003\000\028\000\002\000\029\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\188\000\000\000\
\\007\000\189\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 191
val numrules = 88
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | STRING of  (string)
 | CHAR of  (char) | REAL of  (real) | INT of  (int)
 | DATACONARG of  (string) | DATACON of  (string) | ID of  (string)
 | AtExp_seq1 of  (exp) | AtExp of  (exp) | InfixExp of  (exp)
 | PatFieldList' of  ( ( string * pat )  list)
 | PatFieldList of  ( ( string * pat )  list)
 | PatList' of  (pat list) | PatList of  (pat list) | Pat of  (pat)
 | DeclList of  (decl list) | Decl of  (decl)
 | PMRule of  ( ( pat * exp ) ) | PMatch of  ( ( pat * exp )  list)
 | FieldList' of  ( ( string * exp )  list)
 | FieldList of  ( ( string * exp )  list)
 | ExpComma_seq2 of  (exp list) | ExpComma_seq1 of  (exp list)
 | Exp of  (exp) | Tuple of  (exp) | AtomicExp of  (exp)
 | Unops of  (exp) | Binops of  (exp) | Constant of  (const)
 | TypeFieldList' of  ( ( string * typ )  list)
 | TypeFieldList of  ( ( string * typ )  list)
 | TypeList' of  (typ list) | TypeList of  (typ list) | Type of  (typ)
 | Start of  (top_level option)
end
type svalue = MlyValue.svalue
type result = top_level option
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 50) => true | _ => false
val showTerminal =
fn (T 0) => "KW_int"
  | (T 1) => "KW_real"
  | (T 2) => "KW_string"
  | (T 3) => "KW_char"
  | (T 4) => "KW_fn"
  | (T 5) => "KW_case"
  | (T 6) => "KW_of"
  | (T 7) => "KW_let"
  | (T 8) => "KW_in"
  | (T 9) => "KW_end"
  | (T 10) => "KW_val"
  | (T 11) => "KW_fun"
  | (T 12) => "KW_ref"
  | (T 13) => "KW_not"
  | (T 14) => "KW_if"
  | (T 15) => "KW_then"
  | (T 16) => "KW_else"
  | (T 17) => "KW_unit"
  | (T 18) => "KW_error"
  | (T 19) => "ID"
  | (T 20) => "DATACON"
  | (T 21) => "DATACONARG"
  | (T 22) => "LBRACE"
  | (T 23) => "RBRACE"
  | (T 24) => "INT"
  | (T 25) => "REAL"
  | (T 26) => "CHAR"
  | (T 27) => "HASH"
  | (T 28) => "UNDERSCORE"
  | (T 29) => "COMMA"
  | (T 30) => "COLON"
  | (T 31) => "LPAREN"
  | (T 32) => "RPAREN"
  | (T 33) => "BAR"
  | (T 34) => "TIMES"
  | (T 35) => "PLUS"
  | (T 36) => "MINUS"
  | (T 37) => "ARROW"
  | (T 38) => "DARROW"
  | (T 39) => "CARET"
  | (T 40) => "EQSIGN"
  | (T 41) => "BANG"
  | (T 42) => "ASSGN"
  | (T 43) => "STRING"
  | (T 44) => "LESS"
  | (T 45) => "LESSEQ"
  | (T 46) => "GREATER"
  | (T 47) => "GREATEREQ"
  | (T 48) => "NEG"
  | (T 49) => "SEMICOLON"
  | (T 50) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 50) $$ (T 49) $$ (T 48) $$ (T 47) $$ (T 46) $$ (T 45) $$ (T 44)
 $$ (T 42) $$ (T 41) $$ (T 40) $$ (T 39) $$ (T 38) $$ (T 37) $$ (T 36)
 $$ (T 35) $$ (T 34) $$ (T 33) $$ (T 32) $$ (T 31) $$ (T 30) $$ (T 29)
 $$ (T 28) $$ (T 27) $$ (T 23) $$ (T 22) $$ (T 18) $$ (T 17) $$ (T 16)
 $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9)
 $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2) $$ (T 
1) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( _, _, OptSemi1right)) :: ( _, ( MlyValue.Exp Exp, 
Exp1left, _)) :: rest671)) => let val  result = MlyValue.Start (
SOME (Exp_t (Exp)))
 in ( LrTable.NT 0, ( result, Exp1left, OptSemi1right), rest671)
end
|  ( 1, ( ( _, ( _, _, OptSemi1right)) :: ( _, ( MlyValue.DeclList 
DeclList, DeclList1left, _)) :: rest671)) => let val  result = 
MlyValue.Start (SOME (Decl_t (DeclList)))
 in ( LrTable.NT 0, ( result, DeclList1left, OptSemi1right), rest671)

end
|  ( 2, ( ( _, ( _, SEMICOLON1left, SEMICOLON1right)) :: rest671)) =>
 let val  result = MlyValue.ntVOID ()
 in ( LrTable.NT 1, ( result, SEMICOLON1left, SEMICOLON1right), 
rest671)
end
|  ( 3, ( rest671)) => let val  result = MlyValue.ntVOID ()
 in ( LrTable.NT 1, ( result, defaultPos, defaultPos), rest671)
end
|  ( 4, ( ( _, ( _, KW_int1left, KW_int1right)) :: rest671)) => let
 val  result = MlyValue.Type (Int_t)
 in ( LrTable.NT 2, ( result, KW_int1left, KW_int1right), rest671)
end
|  ( 5, ( ( _, ( _, KW_real1left, KW_real1right)) :: rest671)) => let
 val  result = MlyValue.Type (Real_t)
 in ( LrTable.NT 2, ( result, KW_real1left, KW_real1right), rest671)

end
|  ( 6, ( ( _, ( _, KW_string1left, KW_string1right)) :: rest671)) =>
 let val  result = MlyValue.Type (String_t)
 in ( LrTable.NT 2, ( result, KW_string1left, KW_string1right), 
rest671)
end
|  ( 7, ( ( _, ( _, KW_char1left, KW_char1right)) :: rest671)) => let
 val  result = MlyValue.Type (Char_t)
 in ( LrTable.NT 2, ( result, KW_char1left, KW_char1right), rest671)

end
|  ( 8, ( ( _, ( _, KW_unit1left, KW_unit1right)) :: rest671)) => let
 val  result = MlyValue.Type (Tuple_t [])
 in ( LrTable.NT 2, ( result, KW_unit1left, KW_unit1right), rest671)

end
|  ( 9, ( ( _, ( _, _, KW_ref1right)) :: ( _, ( MlyValue.Type Type, 
Type1left, _)) :: rest671)) => let val  result = MlyValue.Type (
Ref_t (Type))
 in ( LrTable.NT 2, ( result, Type1left, KW_ref1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.Type (Id_t (ID))
 in ( LrTable.NT 2, ( result, ID1left, ID1right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.Type Type2, _, Type2right)) :: _ :: ( _, ( 
MlyValue.Type Type1, Type1left, _)) :: rest671)) => let val  result = 
MlyValue.Type (Fn_t (Type1,Type2))
 in ( LrTable.NT 2, ( result, Type1left, Type2right), rest671)
end
|  ( 12, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.TypeList 
TypeList, _, _)) :: _ :: ( _, ( MlyValue.Type Type, _, _)) :: ( _, ( _
, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.Type (
Tuple_t(Type::TypeList))
 in ( LrTable.NT 2, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 13, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( 
MlyValue.TypeFieldList TypeFieldList, _, _)) :: ( _, ( _, LBRACE1left,
 _)) :: rest671)) => let val  result = MlyValue.Type (
Record_t (TypeFieldList))
 in ( LrTable.NT 2, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 14, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.Type Type, _
, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.Type (Type)
 in ( LrTable.NT 2, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.TypeList TypeList, _, TypeList1right)) :: _
 :: ( _, ( MlyValue.Type Type, Type1left, _)) :: rest671)) => let val 
 result = MlyValue.TypeList (Type::TypeList)
 in ( LrTable.NT 3, ( result, Type1left, TypeList1right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.Type Type, Type1left, Type1right)) :: 
rest671)) => let val  result = MlyValue.TypeList ([Type])
 in ( LrTable.NT 3, ( result, Type1left, Type1right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.TypeFieldList' TypeFieldList', _, 
TypeFieldList'1right)) :: ( _, ( MlyValue.Type Type, _, _)) :: _ :: (
 _, ( MlyValue.ID ID, ID1left, _)) :: rest671)) => let val  result = 
MlyValue.TypeFieldList ((ID,Type)::TypeFieldList')
 in ( LrTable.NT 5, ( result, ID1left, TypeFieldList'1right), rest671)

end
|  ( 18, ( ( _, ( MlyValue.TypeFieldList' TypeFieldList', _, 
TypeFieldList'1right)) :: ( _, ( MlyValue.Type Type, _, _)) :: _ :: (
 _, ( MlyValue.ID ID, _, _)) :: ( _, ( _, COMMA1left, _)) :: rest671))
 => let val  result = MlyValue.TypeFieldList' (
(ID,Type)::TypeFieldList')
 in ( LrTable.NT 6, ( result, COMMA1left, TypeFieldList'1right), 
rest671)
end
|  ( 19, ( rest671)) => let val  result = MlyValue.TypeFieldList' ([])
 in ( LrTable.NT 6, ( result, defaultPos, defaultPos), rest671)
end
|  ( 20, ( ( _, ( MlyValue.INT INT, INT1left, INT1right)) :: rest671))
 => let val  result = MlyValue.Constant (Int_c (INT))
 in ( LrTable.NT 7, ( result, INT1left, INT1right), rest671)
end
|  ( 21, ( ( _, ( MlyValue.REAL REAL, REAL1left, REAL1right)) :: 
rest671)) => let val  result = MlyValue.Constant (Real_c (REAL))
 in ( LrTable.NT 7, ( result, REAL1left, REAL1right), rest671)
end
|  ( 22, ( ( _, ( MlyValue.STRING STRING, STRING1left, STRING1right))
 :: rest671)) => let val  result = MlyValue.Constant (
String_c (STRING))
 in ( LrTable.NT 7, ( result, STRING1left, STRING1right), rest671)
end
|  ( 23, ( ( _, ( MlyValue.CHAR CHAR, CHAR1left, CHAR1right)) :: 
rest671)) => let val  result = MlyValue.Constant (Char_c (CHAR))
 in ( LrTable.NT 7, ( result, CHAR1left, CHAR1right), rest671)
end
|  ( 24, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1, Plus, InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 25, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1, Minus, InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 26, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1, Times, InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 27, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1, Equal, InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 28, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1, Concat, InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 29, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1, LessThan, InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 30, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1,
                                 LessThanEq, InfixExp2)
)
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 31, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1,
                                  GreaterThan, InfixExp2)
)
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 32, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Binop_e(InfixExp1,
                                    GreaterThanEq, InfixExp2)
)
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 33, ( ( _, ( MlyValue.InfixExp InfixExp2, _, InfixExp2right)) ::
 _ :: ( _, ( MlyValue.InfixExp InfixExp1, InfixExp1left, _)) :: 
rest671)) => let val  result = MlyValue.Binops (
Assign_e (InfixExp1,InfixExp2))
 in ( LrTable.NT 8, ( result, InfixExp1left, InfixExp2right), rest671)

end
|  ( 34, ( ( _, ( MlyValue.AtExp AtExp, _, AtExp1right)) :: ( _, ( _, 
KW_not1left, _)) :: rest671)) => let val  result = MlyValue.Unops (
Unop_e(Not, AtExp))
 in ( LrTable.NT 9, ( result, KW_not1left, AtExp1right), rest671)
end
|  ( 35, ( ( _, ( MlyValue.AtExp AtExp, _, AtExp1right)) :: ( _, ( _, 
NEG1left, _)) :: rest671)) => let val  result = MlyValue.Unops (
Unop_e(Neg, AtExp))
 in ( LrTable.NT 9, ( result, NEG1left, AtExp1right), rest671)
end
|  ( 36, ( ( _, ( MlyValue.AtExp AtExp, _, AtExp1right)) :: ( _, ( _, 
KW_ref1left, _)) :: rest671)) => let val  result = MlyValue.Unops (
Ref_e (AtExp))
 in ( LrTable.NT 9, ( result, KW_ref1left, AtExp1right), rest671)
end
|  ( 37, ( ( _, ( MlyValue.AtExp AtExp, _, AtExp1right)) :: ( _, ( _, 
KW_error1left, _)) :: rest671)) => let val  result = MlyValue.Unops (
Error_e (AtExp))
 in ( LrTable.NT 9, ( result, KW_error1left, AtExp1right), rest671)

end
|  ( 38, ( ( _, ( MlyValue.AtExp AtExp, _, AtExp1right)) :: ( _, ( _, 
BANG1left, _)) :: rest671)) => let val  result = MlyValue.Unops (
Deref_e (AtExp))
 in ( LrTable.NT 9, ( result, BANG1left, AtExp1right), rest671)
end
|  ( 39, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.AtomicExp (Id_e(ID))
 in ( LrTable.NT 10, ( result, ID1left, ID1right), rest671)
end
|  ( 40, ( ( _, ( MlyValue.Constant Constant, Constant1left, 
Constant1right)) :: rest671)) => let val  result = MlyValue.AtomicExp
 (Const_e(Constant))
 in ( LrTable.NT 10, ( result, Constant1left, Constant1right), rest671
)
end
|  ( 41, ( ( _, ( MlyValue.AtomicExp AtomicExp, AtomicExp1left, 
AtomicExp1right)) :: rest671)) => let val  result = MlyValue.AtExp (
AtomicExp)
 in ( LrTable.NT 27, ( result, AtomicExp1left, AtomicExp1right), 
rest671)
end
|  ( 42, ( ( _, ( _, _, KW_end1right)) :: ( _, ( MlyValue.Exp Exp, _,
 _)) :: _ :: ( _, ( MlyValue.DeclList DeclList, _, _)) :: ( _, ( _, 
KW_let1left, _)) :: rest671)) => let val  result = MlyValue.AtExp (
Let_e (DeclList,Exp))
 in ( LrTable.NT 27, ( result, KW_let1left, KW_end1right), rest671)

end
|  ( 43, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.Exp Exp, _,
 _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.AtExp (Exp)
 in ( LrTable.NT 27, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 44, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _))
 :: rest671)) => let val  result = MlyValue.AtExp (Tuple_e [])
 in ( LrTable.NT 27, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 45, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( 
MlyValue.ExpComma_seq2 ExpComma_seq2, _, _)) :: ( _, ( _, LPAREN1left,
 _)) :: rest671)) => let val  result = MlyValue.AtExp (
Tuple_e (ExpComma_seq2))
 in ( LrTable.NT 27, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 46, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.FieldList 
FieldList, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let
 val  result = MlyValue.AtExp (Record_e (FieldList))
 in ( LrTable.NT 27, ( result, LBRACE1left, RBRACE1right), rest671)

end
|  ( 47, ( ( _, ( MlyValue.DATACON DATACON, DATACON1left, 
DATACON1right)) :: rest671)) => let val  result = MlyValue.AtExp (
DataCon_e (DATACON, NONE))
 in ( LrTable.NT 27, ( result, DATACON1left, DATACON1right), rest671)

end
|  ( 48, ( ( _, ( MlyValue.Unops Unops, Unops1left, Unops1right)) :: 
rest671)) => let val  result = MlyValue.AtExp (Unops)
 in ( LrTable.NT 27, ( result, Unops1left, Unops1right), rest671)
end
|  ( 49, ( ( _, ( MlyValue.AtExp AtExp, _, AtExp1right)) :: ( _, ( 
MlyValue.AtExp_seq1 AtExp_seq1, AtExp_seq11left, _)) :: rest671)) =>
 let val  result = MlyValue.AtExp_seq1 (App_e (AtExp_seq1,AtExp))
 in ( LrTable.NT 28, ( result, AtExp_seq11left, AtExp1right), rest671)

end
|  ( 50, ( ( _, ( MlyValue.AtExp AtExp, AtExp1left, AtExp1right)) :: 
rest671)) => let val  result = MlyValue.AtExp_seq1 (AtExp)
 in ( LrTable.NT 28, ( result, AtExp1left, AtExp1right), rest671)
end
|  ( 51, ( ( _, ( MlyValue.AtExp_seq1 AtExp_seq1, AtExp_seq11left, 
AtExp_seq11right)) :: rest671)) => let val  result = MlyValue.InfixExp
 (AtExp_seq1)
 in ( LrTable.NT 26, ( result, AtExp_seq11left, AtExp_seq11right), 
rest671)
end
|  ( 52, ( ( _, ( MlyValue.Binops Binops, Binops1left, Binops1right))
 :: rest671)) => let val  result = MlyValue.InfixExp (Binops)
 in ( LrTable.NT 26, ( result, Binops1left, Binops1right), rest671)

end
|  ( 53, ( ( _, ( MlyValue.InfixExp InfixExp, InfixExp1left, 
InfixExp1right)) :: rest671)) => let val  result = MlyValue.Exp (
InfixExp)
 in ( LrTable.NT 12, ( result, InfixExp1left, InfixExp1right), rest671
)
end
|  ( 54, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: ( _, ( 
MlyValue.INT INT, _, _)) :: ( _, ( _, HASH1left, _)) :: rest671)) =>
 let val  result = MlyValue.Exp (Ith_e (INT,Exp))
 in ( LrTable.NT 12, ( result, HASH1left, Exp1right), rest671)
end
|  ( 55, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: ( _, ( 
MlyValue.ID ID, _, _)) :: ( _, ( _, HASH1left, _)) :: rest671)) => let
 val  result = MlyValue.Exp (Field_e (ID,Exp,ref (NONE)))
 in ( LrTable.NT 12, ( result, HASH1left, Exp1right), rest671)
end
|  ( 56, ( ( _, ( MlyValue.Exp Exp3, _, Exp3right)) :: _ :: ( _, ( 
MlyValue.Exp Exp2, _, _)) :: _ :: ( _, ( MlyValue.Exp Exp1, _, _)) :: 
( _, ( _, KW_if1left, _)) :: rest671)) => let val  result = 
MlyValue.Exp ( If_e (Exp1,Exp2,Exp3))
 in ( LrTable.NT 12, ( result, KW_if1left, Exp3right), rest671)
end
|  ( 57, ( ( _, ( MlyValue.PMatch PMatch, _, PMatch1right)) :: _ :: (
 _, ( MlyValue.Exp Exp, _, _)) :: ( _, ( _, KW_case1left, _)) :: 
rest671)) => let val  result = MlyValue.Exp (Case_e (Exp,PMatch))
 in ( LrTable.NT 12, ( result, KW_case1left, PMatch1right), rest671)

end
|  ( 58, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: _ :: _ :: ( _, (
 MlyValue.Type Type, _, _)) :: _ :: ( _, ( MlyValue.ID ID, _, _)) :: _
 :: ( _, ( _, KW_fn1left, _)) :: rest671)) => let val  result = 
MlyValue.Exp (Fn_e (ID,Type,Exp))
 in ( LrTable.NT 12, ( result, KW_fn1left, Exp1right), rest671)
end
|  ( 59, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: _ :: _ :: _ :: (
 _, ( _, KW_fn1left, _)) :: rest671)) => let val  result = 
MlyValue.Exp (Fn_e ("()",Tuple_t [],Exp))
 in ( LrTable.NT 12, ( result, KW_fn1left, Exp1right), rest671)
end
|  ( 60, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: ( _, ( 
MlyValue.DATACONARG DATACONARG, DATACONARG1left, _)) :: rest671)) =>
 let val  result = MlyValue.Exp (DataCon_e (DATACONARG, SOME (Exp)))
 in ( LrTable.NT 12, ( result, DATACONARG1left, Exp1right), rest671)

end
|  ( 61, ( ( _, ( MlyValue.ExpComma_seq1 ExpComma_seq1, _, 
ExpComma_seq11right)) :: _ :: ( _, ( MlyValue.Exp Exp, Exp1left, _))
 :: rest671)) => let val  result = MlyValue.ExpComma_seq1 (
Exp::ExpComma_seq1)
 in ( LrTable.NT 13, ( result, Exp1left, ExpComma_seq11right), rest671
)
end
|  ( 62, ( ( _, ( MlyValue.Exp Exp, Exp1left, Exp1right)) :: rest671))
 => let val  result = MlyValue.ExpComma_seq1 ([Exp])
 in ( LrTable.NT 13, ( result, Exp1left, Exp1right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.ExpComma_seq1 ExpComma_seq1, _, 
ExpComma_seq11right)) :: _ :: ( _, ( MlyValue.Exp Exp, Exp1left, _))
 :: rest671)) => let val  result = MlyValue.ExpComma_seq2 (
Exp::ExpComma_seq1)
 in ( LrTable.NT 14, ( result, Exp1left, ExpComma_seq11right), rest671
)
end
|  ( 64, ( ( _, ( MlyValue.FieldList' FieldList', _, FieldList'1right)
) :: ( _, ( MlyValue.Exp Exp, _, _)) :: _ :: ( _, ( MlyValue.ID ID, 
ID1left, _)) :: rest671)) => let val  result = MlyValue.FieldList (
(ID,Exp)::FieldList')
 in ( LrTable.NT 15, ( result, ID1left, FieldList'1right), rest671)

end
|  ( 65, ( ( _, ( MlyValue.FieldList' FieldList', _, FieldList'1right)
) :: ( _, ( MlyValue.Exp Exp, _, _)) :: _ :: ( _, ( MlyValue.ID ID, _,
 _)) :: ( _, ( _, COMMA1left, _)) :: rest671)) => let val  result = 
MlyValue.FieldList' ((ID,Exp)::FieldList')
 in ( LrTable.NT 16, ( result, COMMA1left, FieldList'1right), rest671)

end
|  ( 66, ( rest671)) => let val  result = MlyValue.FieldList' ([])
 in ( LrTable.NT 16, ( result, defaultPos, defaultPos), rest671)
end
|  ( 67, ( ( _, ( MlyValue.PMatch PMatch, _, PMatch1right)) :: _ :: (
 _, ( MlyValue.PMRule PMRule, PMRule1left, _)) :: rest671)) => let
 val  result = MlyValue.PMatch ((PMRule::PMatch))
 in ( LrTable.NT 17, ( result, PMRule1left, PMatch1right), rest671)

end
|  ( 68, ( ( _, ( MlyValue.PMRule PMRule, PMRule1left, PMRule1right))
 :: rest671)) => let val  result = MlyValue.PMatch ([PMRule])
 in ( LrTable.NT 17, ( result, PMRule1left, PMRule1right), rest671)

end
|  ( 69, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: _ :: ( _, ( 
MlyValue.Pat Pat, Pat1left, _)) :: rest671)) => let val  result = 
MlyValue.PMRule ((Pat,Exp))
 in ( LrTable.NT 18, ( result, Pat1left, Exp1right), rest671)
end
|  ( 70, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: _ :: ( _, ( 
MlyValue.Pat Pat, _, _)) :: ( _, ( _, KW_val1left, _)) :: rest671)) =>
 let val  result = MlyValue.Decl (Val_d (Pat,Exp))
 in ( LrTable.NT 19, ( result, KW_val1left, Exp1right), rest671)
end
|  ( 71, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: _ :: ( _, ( 
MlyValue.Type Type2, _, _)) :: _ :: _ :: ( _, ( MlyValue.Type Type1, _
, _)) :: _ :: ( _, ( MlyValue.ID ID2, _, _)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( _, KW_fun1left, _)) :: rest671)) =>
 let val  result = MlyValue.Decl (
Fun_d (({name=ID1,ret_typ=Type2,arg=ID2,arg_typ=Type1},Exp)))
 in ( LrTable.NT 19, ( result, KW_fun1left, Exp1right), rest671)
end
|  ( 72, ( ( _, ( MlyValue.Exp Exp, _, Exp1right)) :: _ :: ( _, ( 
MlyValue.Type Type, _, _)) :: _ :: _ :: _ :: ( _, ( MlyValue.ID ID, _,
 _)) :: ( _, ( _, KW_fun1left, _)) :: rest671)) => let val  result = 
MlyValue.Decl (
Fun_d (({name=ID,ret_typ=Type,arg="",arg_typ=Tuple_t []},Exp)))
 in ( LrTable.NT 19, ( result, KW_fun1left, Exp1right), rest671)
end
|  ( 73, ( ( _, ( MlyValue.DeclList DeclList, _, DeclList1right)) :: (
 _, ( MlyValue.Decl Decl, Decl1left, _)) :: rest671)) => let val  
result = MlyValue.DeclList (Decl::DeclList)
 in ( LrTable.NT 20, ( result, Decl1left, DeclList1right), rest671)

end
|  ( 74, ( rest671)) => let val  result = MlyValue.DeclList ([])
 in ( LrTable.NT 20, ( result, defaultPos, defaultPos), rest671)
end
|  ( 75, ( ( _, ( _, UNDERSCORE1left, UNDERSCORE1right)) :: rest671))
 => let val  result = MlyValue.Pat (Wild_p)
 in ( LrTable.NT 21, ( result, UNDERSCORE1left, UNDERSCORE1right), 
rest671)
end
|  ( 76, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) =>
 let val  result = MlyValue.Pat (Id_p (ID))
 in ( LrTable.NT 21, ( result, ID1left, ID1right), rest671)
end
|  ( 77, ( ( _, ( MlyValue.INT INT, INT1left, INT1right)) :: rest671))
 => let val  result = MlyValue.Pat (Const_p (INT))
 in ( LrTable.NT 21, ( result, INT1left, INT1right), rest671)
end
|  ( 78, ( ( _, ( MlyValue.Pat Pat, _, Pat1right)) :: ( _, ( 
MlyValue.DATACONARG DATACONARG, DATACONARG1left, _)) :: rest671)) =>
 let val  result = MlyValue.Pat (DataCon_p (DATACONARG,SOME (Pat)))
 in ( LrTable.NT 21, ( result, DATACONARG1left, Pat1right), rest671)

end
|  ( 79, ( ( _, ( MlyValue.DATACON DATACON, DATACON1left, 
DATACON1right)) :: rest671)) => let val  result = MlyValue.Pat (
DataCon_p (DATACON,NONE))
 in ( LrTable.NT 21, ( result, DATACON1left, DATACON1right), rest671)

end
|  ( 80, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.PatList 
PatList, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val 
 result = MlyValue.Pat (
case PatList of [p] => p | _ => Tuple_p (PatList))
 in ( LrTable.NT 21, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 81, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.PatFieldList
 PatFieldList, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) =>
 let val  result = MlyValue.Pat (Record_p (PatFieldList))
 in ( LrTable.NT 21, ( result, LBRACE1left, RBRACE1right), rest671)

end
|  ( 82, ( ( _, ( MlyValue.PatList' PatList', _, PatList'1right)) :: (
 _, ( MlyValue.Pat Pat, Pat1left, _)) :: rest671)) => let val  result
 = MlyValue.PatList (Pat::PatList')
 in ( LrTable.NT 22, ( result, Pat1left, PatList'1right), rest671)
end
|  ( 83, ( ( _, ( MlyValue.PatList' PatList', _, PatList'1right)) :: (
 _, ( MlyValue.Pat Pat, _, _)) :: ( _, ( _, COMMA1left, _)) :: rest671
)) => let val  result = MlyValue.PatList' (Pat::PatList')
 in ( LrTable.NT 23, ( result, COMMA1left, PatList'1right), rest671)

end
|  ( 84, ( rest671)) => let val  result = MlyValue.PatList' ([])
 in ( LrTable.NT 23, ( result, defaultPos, defaultPos), rest671)
end
|  ( 85, ( ( _, ( MlyValue.PatFieldList' PatFieldList', _, 
PatFieldList'1right)) :: ( _, ( MlyValue.Pat Pat, _, _)) :: _ :: ( _, 
( MlyValue.ID ID, ID1left, _)) :: rest671)) => let val  result = 
MlyValue.PatFieldList ((ID,Pat)::PatFieldList')
 in ( LrTable.NT 24, ( result, ID1left, PatFieldList'1right), rest671)

end
|  ( 86, ( ( _, ( MlyValue.PatFieldList' PatFieldList', _, 
PatFieldList'1right)) :: ( _, ( MlyValue.Pat Pat, _, _)) :: _ :: ( _, 
( MlyValue.ID ID, _, _)) :: ( _, ( _, COMMA1left, _)) :: rest671)) =>
 let val  result = MlyValue.PatFieldList' ((ID,Pat)::PatFieldList')
 in ( LrTable.NT 25, ( result, COMMA1left, PatFieldList'1right), 
rest671)
end
|  ( 87, ( rest671)) => let val  result = MlyValue.PatFieldList' ([])
 in ( LrTable.NT 25, ( result, defaultPos, defaultPos), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.Start x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : MiniML_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun KW_int (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_real (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_string (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_char (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_fn (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_case (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_of (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_let (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_in (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_end (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_val (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_fun (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_ref (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_not (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_if (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_then (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_else (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_unit (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun KW_error (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.ID i,p1,p2))
fun DATACON (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.DATACON i,p1,p2))
fun DATACONARG (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.DATACONARG i,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun INT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.INT i,p1,p2))
fun REAL (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.REAL i,p1,p2))
fun CHAR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.CHAR i,p1,p2))
fun HASH (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun UNDERSCORE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun BAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun TIMES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID,p1,p2))
fun ARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID,p1,p2))
fun DARROW (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID,p1,p2))
fun CARET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID,p1,p2))
fun EQSIGN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID,p1,p2))
fun BANG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID,p1,p2))
fun ASSGN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID,p1,p2))
fun STRING (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.STRING i,p1,p2))
fun LESS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID,p1,p2))
fun LESSEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 45,(
ParserData.MlyValue.VOID,p1,p2))
fun GREATER (p1,p2) = Token.TOKEN (ParserData.LrTable.T 46,(
ParserData.MlyValue.VOID,p1,p2))
fun GREATEREQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 47,(
ParserData.MlyValue.VOID,p1,p2))
fun NEG (p1,p2) = Token.TOKEN (ParserData.LrTable.T 48,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 49,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 50,(
ParserData.MlyValue.VOID,p1,p2))
end
end
