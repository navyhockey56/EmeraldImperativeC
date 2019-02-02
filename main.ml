open Ast
open Instr
open Disassembler
open Compiler

(*********************************************************************
I pledge on my honor that I have not given or received any unauthorized assistance
on this assignment - Will Dengler
*********************************************************************)





let rec output_expr o = function
  | EInt i -> Printf.fprintf o "%d" i
  | EString s -> Printf.fprintf o "\"%s\"" s
  | ELocRd x -> output_string o x
  | ELocWr (x, e) ->
     Printf.fprintf o "%s = (%a)" x output_expr e
  | EIf (e1, e2, e3) ->
     Printf.fprintf o "if %a then %a else %a end" output_expr e1
		    output_expr e2 output_expr e3
  | EWhile (e1, e2) ->
     Printf.fprintf o "while %a do %a end" output_expr e1 output_expr e2
  | ESeq (e1, e2) -> Printf.fprintf o "%a; %a" output_expr e1 output_expr e2
  | EBinOp (e1, b, e2) ->
     Printf.fprintf o "(%a) %a (%a)" output_expr e1 output_bop b output_expr e2
  | ETabRd (e1, e2) ->
     Printf.fprintf o "%a[%a]" output_expr e1 output_expr e2
  | ETabWr (e1, e2, e3) ->
     Printf.fprintf o "%a[%a] = (%a)" output_expr e1 output_expr e2 output_expr e3
  | ECall (f, es) ->
      Printf.fprintf o "%s(%a)" f output_exprs es

and output_bop o = function
  | BPlus -> Printf.fprintf o "+"
  | BMinus -> Printf.fprintf o "-"
  | BTimes -> Printf.fprintf o "*"
  | BDiv -> Printf.fprintf o "/"
  | BEq -> Printf.fprintf o "=="
  | BLt -> Printf.fprintf o "<"
  | BLeq -> Printf.fprintf o "<="

and output_exprs o = function
    [] -> ()
  | [e] -> output_expr o e
  | e::es -> Printf.fprintf o "%a, %a" output_expr e output_exprs es

and output_arg o = function
    s -> Printf.fprintf o "%s" s

and output_args o = function
  | [] -> ()
  | [a] -> output_arg o a
  | a::aa -> Printf.fprintf o "%a, %a" output_arg a output_args aa

and output_fn o ({fn_name=name; fn_args=args; fn_body=body}:simpl_fn) =
  Printf.fprintf o "  def %s(%a)\n %a\n  end\n" name output_args args output_expr body

and output_fns o = function
    [] -> ()
  | [f] -> Printf.fprintf o "%a" output_fn f
  | f::fs -> Printf.fprintf o "%a\n%a" output_fn f output_fns fs

and print_program (fs:simpl_prog) =
  Printf.printf "%a\n" output_fns fs

(*********************************************************************)

let rec determine_file_name file_name = 
	let length = String.length file_name in 
	match (String.index_from_opt file_name 0 '/') with 
		| None -> String.sub file_name 0 (length - 3)
		| Some i -> 
			let file_name = String.sub file_name (i + 1) (length - i - 1) in 
			determine_file_name file_name 
;;


let parse_file name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let (p:simpl_prog) = Parser.main Lexer.token lexbuf in
    close_in chan;
    p

let main () =
	(* Retrieve the input file *)
	let file_name = Sys.argv.(1) in

	(* Determine the files name within the context of its parent directory *) 
	let simple_file_name = determine_file_name file_name in
  
  (* Parse the input file *)
  let p = parse_file file_name in

  (* Compile the program *)
  let (p':Instr.prog) = Compiler.compile_prog p in

  (* Open the output file *)
  let out_chan = open_out (simple_file_name ^ ".evm") in
  
  (* Dump the output program into the file*)
  disassemble out_chan p'
;;

main ()
