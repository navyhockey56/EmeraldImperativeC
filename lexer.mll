{
 open Parser
 exception Eof
}
rule token = parse
  [' ' '\t' '\n' '\r']	{ token lexbuf }
| "if" { IF }
| "then" { THEN }
| "else" { ELSE }
| "end" { END }
| "while" { WHILE }
| "def" { DEF }
| "do" { DO }
| '(' { LP }
| ')' { RP }
| '[' { LB }
| ']' { RB }
| ',' { COMMA }
| ';' { SEMI }
| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| "==" { EQ }
| '<' { LT }
| "<=" { LEQ }
| '=' { ASSN }
| '"' [^'"']* '"' as lxm { STR(Scanf.unescaped(String.sub lxm 1 ((String.length lxm) - 2))) }
| ('-'?)['0'-'9']+ as lxm { INT(int_of_string lxm) }
| ['A'-'Z''a'-'z''_']+ as lxm { ID(lxm) }
| eof { EOF }
| _ as lxm { Printf.printf "Illegal character %c" lxm; failwith "Bad input" }

