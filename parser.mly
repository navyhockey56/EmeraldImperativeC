%{
  open Ast
%}

%token <int> INT
%token <string> STR ID
%token IF THEN ELSE END WHILE DEF DO
%token LP RP LB RB COMMA SEMI
%token PLUS MINUS TIMES DIV EQ LT LEQ ASSN
%token EOF
%start main
%type <Ast.simpl_prog> main
%right SEMI
%right ASSN
%left PLUS MINUS
%left TIMES DIV
%left EQ LT LEQ
%nonassoc LB
%%
main:
 fns EOF { $1 }
;
fns:
  { [] }
| fn fns { $1::$2 }
fn:
  DEF ID LP ids RP exprs END {
    { fn_name = $2;
      fn_args = $4;
      fn_body = $6 }
  }
;
ids:
  { [] }
| ID  { [$1] }
| ID COMMA ids { $1::$3 }
;
exprs:
  expr { $1 }
| expr SEMI exprs { ESeq($1, $3) }
;
expr:
| INT { EInt $1 }
| STR { EString $1 }
| ID { ELocRd $1 }
| ID ASSN expr { ELocWr($1, $3) }
| IF expr THEN exprs ELSE exprs END { EIf($2, $4, $6) }
| WHILE expr DO exprs END { EWhile($2, $4) }
| expr PLUS expr { EBinOp($1, BPlus, $3) }
| expr MINUS expr { EBinOp($1, BMinus, $3) }
| expr TIMES expr { EBinOp($1, BTimes, $3) }
| expr DIV expr { EBinOp($1, BDiv, $3) }
| expr EQ expr { EBinOp($1, BEq, $3) }
| expr LT expr { EBinOp($1, BLt, $3) }
| expr LEQ expr { EBinOp($1, BLeq, $3) }
| expr LB expr RB { ETabRd($1, $3) }
| expr LB expr RB ASSN expr { ETabWr($1, $3, $6) }
| ID LP params RP { ECall($1, $3) }
| LP exprs RP { $2 }
;
params:
  { [] }
| expr { [$1] }
| expr COMMA params { $1::$3 }
