(* ============================================================================================== *) 
datatype lexresult = SHELL of string * string * {line: word, column: word};
val error          = fn x => TextIO.output(TextIO.stdOut,x ^ "\n")
val eof            = fn () => SHELL("","eof",getNextTokenPos(""))
(* ============================================================================================== *)
(* ------------------------------------------------------------------ *)
(* assumes that ">" does not occur as part of a nonterminal symbol *)
fun generateSchemaTokenName( yytext ) =
    let
	fun split(x, []   )   = raise General.Fail("an_error")
          | split(x, y::ys)   = if x=y then ys else split(x,ys);
													
	fun splitFirst(symbol,[])     = [] (* symbol was not in the input list *)
          | splitFirst(symbol,x::xs)  = if x = symbol 
					then (* found split point *)
                                            []
					else (* keep looking      *)
                                            x::splitFirst(symbol,xs);
																		
        val s0    = explode(yytext);
        val s1    = split(#"<",s0);
        val s2    = splitFirst(#">",s1);  
    in
        implode(explode("!#schema_variable_") @ s2)        
    end;
	
(* ------------------------------------------------------------------ *)

(* ============================================================================================== *)
%%
%header (functor Target_LexFn(val getNextTokenPos : string -> {line: word, column: word}));

Integer         = 0 | [1-9][0-9]*;
Variable        = [A-Za-z][A-Za-z0-9_]*;
ws              = [\  \t \n];

%%

"("             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
")"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"{"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"}"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
";"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"++"            => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"--"            => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"="             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));

"INTEGER"       => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"BOOLEAN"       => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));

"true"          => ( SHELL( yytext, yytext, getNextTokenPos( yytext)) );
"false"         => ( SHELL( yytext, yytext, getNextTokenPos( yytext)) );

"+"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"-"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"*"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"/"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"MOD"           => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"|"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"^"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"~"             => ( SHELL(yytext, yytext, getNextTokenPos(yytext)) );

"and"           => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"or"            => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"not"           => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));

"<"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
">"             => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"=="            => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"!="            => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));

"if"            => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"else"          => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"while"         => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"for"           => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));
"print"         => ( SHELL( yytext, yytext, getNextTokenPos( yytext )));

{Integer}       => ( SHELL( "Integer"    , yytext, getNextTokenPos(yytext)));
{Variable}      => ( SHELL( "Variable"   , yytext, getNextTokenPos(yytext)));

{ws}+           => ( getNextTokenPos( yytext ); lex());
 .              => ( error( "ignored an unprintable character: " ^ yytext ); getNextTokenPos( yytext ); lex()); 









