open Ast
open Instr
open Disassembler

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
let next_location_func flag = let x = ref (-1) in
	(fun () -> if flag then (x := !x + 1; !x) else (x := 0; !x));;

(*Takes a return instruction and returns the register to be returned*)
let get_register_value = function
	| I_ret r -> r
	| _ -> failwith "coding error: expected return instruction";;

let rec expr_to_instr (body:expr) (args:string list) (next_location:(unit -> int))
(local_map:((string, int) Hashtbl.t)) (bad_names:string list):fn = match body with
	| EInt n ->
		let loc = next_location () in (*get register location*)
		let inst1 = I_const ((`L_Reg loc), (`L_Int n)) in (*load n into register*)
		let inst2 = I_ret (`L_Reg loc) in  (*create return register with n*)
		let instrucs = Array.make 2 inst1 in (*create instruction array*)
		Array.set instrucs 1 inst2; instrucs (*place inst2 in array and return the array*)

	| EString str ->
		let loc = next_location () in (*get register location*)
		let inst1 = I_const ((`L_Reg loc), (`L_Str str)) in (*load str into register*)
		let inst2 = I_ret (`L_Reg loc) in  (*create return register with str*)
		let instrucs = Array.make 2 inst1 in (*create instruction array*)
		Array.set instrucs 1 inst2; instrucs (*place inst2 in array and return the array*)

	| ELocRd id ->
		(*checks if id has been mapped to a register in the function call, if so
		then creates a return instruction with the mapped register; else, creates a
		return to a non-existant register.*)
		if (Hashtbl.mem local_map id) then ( (*id has a mapping*)
			let loc = (Hashtbl.find local_map id) in (*get register value*)
			[|I_ret (`L_Reg loc)|] (*create and return return instruction*)
		) else (
			let message = "Error: Variable - " ^ id ^ " - is not bound in this environment." in
			let loc = next_location () in
			let load_message = I_const ((`L_Reg loc), (`L_Str message)) in
			let ihalt = I_halt (`L_Reg loc) in
			[|load_message;ihalt|]
		)

	| ELocWr (id, expr) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr expr args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		if (Hashtbl.mem local_map id) then (
			let loc = Hashtbl.find local_map id in
			let inst1 = I_mov ((`L_Reg loc), v1_reg_value) in (*copy the expr's value into new register*)
			let inst2 = I_ret (`L_Reg loc) in (*return the value of the local variable*)

			(*code_of_v1 + [inst1]*)
			let instrucs = Array.append code_of_v1 ([|inst1;inst2|]) in
			instrucs
		) else (
			let loc = next_location () in (*get a fresh register location*)
			(Hashtbl.replace local_map id loc); (*map the id to the register location*)
			let inst1 = I_mov ((`L_Reg loc), v1_reg_value) in (*copy the expr's value into new register*)
			let inst2 = I_ret (`L_Reg loc) in (*return the value of the local variable*)

			(*code_of_v1 + [inst1]*)
			let instrucs = Array.append code_of_v1 ([|inst1;inst2|]) in
			instrucs
		)
	| EIf (exp1, exp2, exp3) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code for both exp1 and exp2 using expr_to_in*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in
		let code_of_v3 = (expr_to_instr exp3 args next_location local_map bad_names) in

		(*if exp1 = 0 jump past code of exp2 - see how code is organized below*)
		let inst1 = I_if_zero (v1_reg_value, (Array.length code_of_v2)) in

		(*code_of_v1 + [|inst1|] + code_of_v2 + code_of_v3 *)
		let instrucs = Array.append code_of_v1 ([|inst1|]) in
		let instrucs = Array.append instrucs code_of_v2 in
		let instrucs = Array.append instrucs code_of_v3 in
		instrucs

	| EWhile (exp1, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code for exp1 using expr_to_in and remove the return instruction*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		(*if exp1 = 0 jump past code of exp2 - see how code is organized below*)
		let inst1 = I_if_zero (v1_reg_value, ((Array.length code_of_v2) + 1)) in
		(*jump -|code_of_v2| -> returns back to inst1*)
		let inst2 = I_jmp (-1 * (2 + (Array.length code_of_v2) + (Array.length code_of_v1))) in
		let inst3 = I_ret (v1_reg_value) in

		(*code_of_v1 + [|inst1|] + code_of_v2 + [jump]*)
		let instrucs = Array.append code_of_v1 ([|inst1|]) in
		let instrucs = Array.append instrucs code_of_v2 in
		let instrucs = Array.append instrucs ([|inst2;inst3|]) in
		instrucs

	| ESeq (exp1, exp2) ->
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in
		(Array.append code_of_v1 code_of_v2)

	| EBinOp (exp1, BPlus, exp2) -> (*USE IS_I AND AN IF STATEMENT TO CREATE ERROR*)
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		let loc = next_location () in
		let add_of_vals = I_add ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|add_of_vals;iret|]
		(*
		let loc1 = next_location () in
		let is_i1 = I_is_int ((`L_Reg loc1), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc1), 4) in

		let loc2 = next_location () in
		let is_i2 = I_is_int ((`L_Reg loc2), v2_reg_value) in
		let check2 = I_if_zero ((`L_Reg loc2), 2) in


		let loc = loc1 in
		let add_of_vals = I_add ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let error_message = "Error: arguments must be integers" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let instrucs = Array.append code_of_v1 code_of_v2 in
		let rest = [|is_i1;check1;is_i2;check2;add_of_vals;iret;load_message;ihalt|] in
		Array.append instrucs rest
		*)

	| EBinOp (exp1, BMinus, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		let loc = next_location () in
		let min_of_vals = I_sub ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|min_of_vals;iret|]

		(*
		let loc1 = next_location () in
		let is_i1 = I_is_int ((`L_Reg loc1), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc1), 4) in

		let loc2 = next_location () in
		let is_i2 = I_is_int ((`L_Reg loc2), v2_reg_value) in
		let check2 = I_if_zero ((`L_Reg loc2), 2) in


		let loc = loc1 in
		let sub_of_vals = I_sub ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let error_message = "Error: arguments must be integers" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let instrucs = Array.append code_of_v1 code_of_v2 in
		let rest = [|is_i1;check1;is_i2;check2;sub_of_vals;iret;load_message;ihalt|] in
		Array.append instrucs rest
		*)

	| EBinOp (exp1, BTimes, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		let loc = next_location () in
		let mul_of_vals = I_mul ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|mul_of_vals;iret|]
		(*
		let loc1 = next_location () in
		let is_i1 = I_is_int ((`L_Reg loc1), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc1), 4) in

		let loc2 = next_location () in
		let is_i2 = I_is_int ((`L_Reg loc2), v2_reg_value) in
		let check2 = I_if_zero ((`L_Reg loc2), 2) in


		let loc = loc1 in
		let mul_of_vals = I_mul ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let error_message = "Error: arguments must be integers" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let instrucs = Array.append code_of_v1 code_of_v2 in
		let rest = [|is_i1;check1;is_i2;check2;mul_of_vals;iret;load_message;ihalt|] in
		Array.append instrucs rest
		*)

	| EBinOp (exp1, BDiv, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		let loc = next_location () in
		let div_of_vals = I_div ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|div_of_vals;iret|]
		(*
		let loc1 = next_location () in
		let is_i1 = I_is_int ((`L_Reg loc1), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc1), 4) in

		let loc2 = next_location () in
		let is_i2 = I_is_int ((`L_Reg loc2), v2_reg_value) in
		let check2 = I_if_zero ((`L_Reg loc2), 2) in


		let loc = loc1 in
		let div_of_vals = I_div ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let error_message = "Error: arguments must be integers" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let instrucs = Array.append code_of_v1 code_of_v2 in
		let rest = [|is_i1;check1;is_i2;check2;div_of_vals;iret;load_message;ihalt|] in
		Array.append instrucs rest
		*)

	| EBinOp (exp1, BEq, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)


		let loc = next_location () in (*get register location*)
		let inst1 = I_eq ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let inst2 = I_ret (`L_Reg loc) in  (*create return register*)

		(*code_of_v1 + code_of_v2 + [|inst1;inst2|]*)
		let instrucs = Array.append code_of_v1 code_of_v2 in
		let instrucs = Array.append instrucs [|inst1;inst2|] in
		instrucs

	| EBinOp (exp1, BLeq, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		let loc = next_location () in
		let leq_of_vals = I_leq ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|leq_of_vals;iret|]

		(*
		let loc1 = next_location () in
		let is_i1 = I_is_int ((`L_Reg loc1), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc1), 4) in

		let loc2 = next_location () in
		let is_i2 = I_is_int ((`L_Reg loc2), v2_reg_value) in 1
		let check2 = I_if_zero ((`L_Reg loc2), 2) in


		let loc = loc1 in
		let leq_of_vals = I_leq ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let error_message = "Error: arguments must be integers" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let instrucs = Array.append code_of_v1 code_of_v2 in
		let rest = [|is_i1;check1;is_i2;check2;leq_of_vals;iret;load_message;ihalt|] in
		Array.append instrucs rest
		*)

	| EBinOp (exp1, BLt, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		let loc = next_location () in
		let lt_of_vals = I_lt ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|lt_of_vals;iret|]

		(*
		let loc1 = next_location () in
		let is_i1 = I_is_int ((`L_Reg loc1), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc1), 4) in

		let loc2 = next_location () in
		let is_i2 = I_is_int ((`L_Reg loc2), v2_reg_value) in
		let check2 = I_if_zero ((`L_Reg loc2), 2) in


		let loc = loc1 in
		let lt_of_vals = I_lt ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		let error_message = "Error: arguments must be integers" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let instrucs = Array.append code_of_v1 code_of_v2 in
		let rest = [|is_i1;check1;is_i2;check2;lt_of_vals;iret;load_message;ihalt|] in
		Array.append instrucs rest
		*)

	| ETabRd (exp1, exp2) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)


		let loc = next_location () in (*get register location*)
		(*let is_tab = I_is_tab ((`L_Reg loc), v1_reg_value) in
		let check1 = I_if_zero ((`L_Reg loc), 4) in
		*)
		let has_loc = I_has_tab ((`L_Reg loc), v1_reg_value, v2_reg_value) in
		let loc1 = next_location () in
		let load_1 = I_const ((`L_Reg loc1), (`L_Int 1)) in
		let sub_1 = I_sub ((`L_Reg loc), (`L_Reg loc), (`L_Reg loc1)) in
		let check2 = I_if_zero ((`L_Reg loc), 2) in

		let error_message = "Error: Invalid input on table read" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in

		let rd_tab = I_rd_tab ((`L_Reg loc), v1_reg_value, v2_reg_value) in (*load add into register*)
		let iret = I_ret (`L_Reg loc) in  (*create return register*)

		(*code_of_v1 + code_of_v2 + [|inst1;inst2|]*)
		let instrucs = Array.append code_of_v1 code_of_v2 in
		Array.append instrucs [|has_loc;load_1;sub_1;check2;load_message;ihalt;rd_tab;iret|]
		(*Array.append instrucs [|is_tab;check1;has_loc;check2;rd_tab;iret;load_message;ihalt|]*)

	| ETabWr (exp1, exp2, exp3) ->
		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v1 = (expr_to_instr exp1 args next_location local_map bad_names) in (*generate instrucs*)
		let v1_reg = (Array.get code_of_v1 ((Array.length code_of_v1) - 1)) in (*get return inst*)
		let v1_reg_value = get_register_value v1_reg in (*get the register*)
		let code_of_v1 = (Array.sub code_of_v1 0 ((Array.length code_of_v1) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v2 = (expr_to_instr exp2 args next_location local_map bad_names) in (*generate instrucs*)
		let v2_reg = (Array.get code_of_v2 ((Array.length code_of_v2) - 1)) in (*get return inst*)
		let v2_reg_value = get_register_value v2_reg in (*get the register*)
		let code_of_v2 = (Array.sub code_of_v2 0 ((Array.length code_of_v2) - 1)) in (*remove return inst*)

		(*generate the code that produces the value of exp using expr_to_int
		then the resulting value of the register will be stored at the end of the result
		in a return instruction. Get the register of the return instruction, then
		remove the return instruction from the produced instructions*)
		let code_of_v3 = (expr_to_instr exp3 args next_location local_map bad_names) in (*generate instrucs*)
		let v3_reg = (Array.get code_of_v3 ((Array.length code_of_v3) - 1)) in (*get return inst*)
		let v3_reg_value = get_register_value v3_reg in (*get the register*)
		let code_of_v3 = (Array.sub code_of_v3 0 ((Array.length code_of_v3) - 1)) in (*remove return inst*)

		(*
		let loc = next_location () in (*get register location*)
		let is_tab = I_is_tab ((`L_Reg loc), v1_reg_value) in
		let check = I_if_zero ((`L_Reg loc), 2) in
		*)
		let wr_tab = I_wr_tab (v1_reg_value, v2_reg_value, v3_reg_value) in (*load add into register*)
		let iret  = I_ret (v3_reg_value) in  (*create return register*)
		(*
		let error_message = "Error: Invalid input on table read" in
		let load_message = I_const ((`L_Reg loc), (`L_Str error_message)) in
		let ihalt = I_halt (`L_Reg loc) in
		*)
		let instrucs = Array.append code_of_v1 code_of_v2 in
		let instrucs = Array.append instrucs code_of_v3 in
		Array.append instrucs [|wr_tab;iret|]
		(*Array.append instrucs [|test1;is_tab;check;wr_tab;iret;load_message;ihalt|]*)

	| ECall ("mktab", exp_list) ->
		if (List.mem "mktab" bad_names) then (

			let instrucs, regs = List.fold_left (fun (instrucs,regs) exp ->
				let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
				let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
				let reg_value = get_register_value reg_instr in (*get the register*)
				let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)
				((Array.append instrucs code_of_exp), (regs@[reg_value]))
			) ([||],[]) exp_list in

			let instrucs = List.fold_left (fun instrucs reg_value ->
				let loc = next_location () in
				let mov = I_mov ((`L_Reg loc), reg_value) in
				(Array.append instrucs [|mov|])
			) instrucs regs in

			let loc = next_location () in
			let iconst = I_const ((`L_Reg loc), (`L_Id "mktab")) in
			let icall = I_call ((`L_Reg loc), (loc - (List.length regs)), (loc - 1)) in
			let iret = I_ret (`L_Reg (loc - (List.length regs))) in
			(Array.append instrucs [|iconst;icall;iret|])

		) else (

			let loc = next_location () in
			let mk_tab = I_mk_tab (`L_Reg loc) in
			let iret = I_ret (`L_Reg loc) in
			[|mk_tab;iret|]
		)



	| ECall ("is_i", exp_list) ->
		if (List.mem "is_i" bad_names) then (

			let instrucs, regs = List.fold_left (fun (instrucs,regs) exp ->
				let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
				let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
				let reg_value = get_register_value reg_instr in (*get the register*)
				let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)
				((Array.append instrucs code_of_exp), (regs@[reg_value]))
			) ([||],[]) exp_list in

			let instrucs = List.fold_left (fun instrucs reg_value ->
				let loc = next_location () in
				let mov = I_mov ((`L_Reg loc), reg_value) in
				(Array.append instrucs [|mov|])
			) instrucs regs in

			let loc = next_location () in
			let iconst = I_const ((`L_Reg loc), (`L_Id "is_i")) in
			let icall = I_call ((`L_Reg loc), (loc - (List.length regs)), (loc - 1)) in
			let iret = I_ret (`L_Reg (loc - (List.length regs))) in
			(Array.append instrucs [|iconst;icall;iret|])

		) else (
			let exp::_ = exp_list in
			let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
			let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
			let reg_value = get_register_value reg_instr in (*get the register*)
			let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)

			let loc = next_location () in
			let is_i = I_is_int ((`L_Reg loc),reg_value) in
			let iret = I_ret (`L_Reg loc) in
			Array.append code_of_exp [|is_i;iret|]
		)

	| ECall ("is_s", exp_list) ->
		if (List.mem "is_s" bad_names) then (

			let instrucs, regs = List.fold_left (fun (instrucs,regs) exp ->
				let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
				let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
				let reg_value = get_register_value reg_instr in (*get the register*)
				let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)
				((Array.append instrucs code_of_exp), (regs@[reg_value]))
			) ([||],[]) exp_list in

			let instrucs = List.fold_left (fun instrucs reg_value ->
				let loc = next_location () in
				let mov = I_mov ((`L_Reg loc), reg_value) in
				(Array.append instrucs [|mov|])
			) instrucs regs in

			let loc = next_location () in
			let iconst = I_const ((`L_Reg loc), (`L_Id "is_s")) in
			let icall = I_call ((`L_Reg loc), (loc - (List.length regs)), (loc - 1)) in
			let iret = I_ret (`L_Reg (loc - (List.length regs))) in
			(Array.append instrucs [|iconst;icall;iret|])

		) else (
			let exp::_ = exp_list in
			let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
			let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
			let reg_value = get_register_value reg_instr in (*get the register*)
			let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)

			let loc = next_location () in
			let is_s = I_is_int ((`L_Reg loc),reg_value) in
			let iret = I_ret (`L_Reg loc) in
			Array.append code_of_exp [|is_s;iret|]
		)

	| ECall ("is_t", exp_list) ->
		if (List.mem "is_t" bad_names) then (

			let instrucs, regs = List.fold_left (fun (instrucs,regs) exp ->
				let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
				let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
				let reg_value = get_register_value reg_instr in (*get the register*)
				let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)
				((Array.append instrucs code_of_exp), (regs@[reg_value]))
			) ([||],[]) exp_list in

			let instrucs = List.fold_left (fun instrucs reg_value ->
				let loc = next_location () in
				let mov = I_mov ((`L_Reg loc), reg_value) in
				(Array.append instrucs [|mov|])
			) instrucs regs in

			let loc = next_location () in
			let iconst = I_const ((`L_Reg loc), (`L_Id "is_t")) in
			let icall = I_call ((`L_Reg loc), (loc - (List.length regs)), (loc - 1)) in
			let iret = I_ret (`L_Reg (loc - (List.length regs))) in
			(Array.append instrucs [|iconst;icall;iret|])

		) else (
			let exp::_ = exp_list in
			let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
			let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
			let reg_value = get_register_value reg_instr in (*get the register*)
			let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)

			let loc = next_location () in
			let is_t = I_is_int ((`L_Reg loc),reg_value) in
			let iret = I_ret (`L_Reg loc) in
			Array.append code_of_exp [|is_t;iret|]
		)

	| ECall (id, exp_list) ->

		let instrucs, regs = List.fold_left (fun (instrucs,regs) exp ->
			let code_of_exp = (expr_to_instr exp args next_location local_map bad_names) in
			let reg_instr = (Array.get code_of_exp ((Array.length code_of_exp) - 1)) in (*get return inst*)
			let reg_value = get_register_value reg_instr in (*get the register*)
			let code_of_exp = (Array.sub code_of_exp 0 ((Array.length code_of_exp) - 1)) in (*remove return inst*)
			((Array.append instrucs code_of_exp), (regs@[reg_value]))
		) ([||],[]) exp_list in

		let instrucs = List.fold_left (fun instrucs reg_value ->
			let loc = next_location () in
			let mov = I_mov ((`L_Reg loc), reg_value) in
			(Array.append instrucs [|mov|])
		) instrucs regs in

		let loc = next_location () in
		let iconst = I_const ((`L_Reg loc), (`L_Id id)) in
		let icall = I_call ((`L_Reg loc), (loc - (List.length regs)), (loc - 1)) in
		let iret = I_ret (`L_Reg (loc - (List.length regs))) in
    (Array.append instrucs [|iconst;icall;iret|])
;;




let rec map_args (tbl:((string, int) Hashtbl.t)) (ids:string list) (next_location:(unit -> int)) =
	match ids with
	| [] -> tbl, next_location
	| id::tail -> (Hashtbl.replace tbl id (next_location ())); map_args tbl tail next_location;;

let rec check_bad_names (bad_names:(string list)) (p:simpl_prog):(string list) =
	match p with
	| [] -> bad_names
	| {fn_name="mktab"; fn_args=args; fn_body=body}::tail ->
		check_bad_names ("mktab"::bad_names) tail
	| {fn_name="is_i"; fn_args=args; fn_body=body}::tail ->
		check_bad_names ("is_i"::bad_names) tail
	| {fn_name="is_s"; fn_args=args; fn_body=body}::tail ->
		check_bad_names ("is_s"::bad_names) tail
	| {fn_name="is_t"; fn_args=args; fn_body=body}::tail ->
		check_bad_names ("is_t"::bad_names) tail
	| _::tail -> check_bad_names bad_names tail

(*Creates a new entry in the rubevm program for the incoming function*)
let compile_instruction ({fn_name=name; fn_args=args; fn_body=body}:simpl_fn)
(rube_prog:prog) (next_location:(unit -> int)) (bad_names:string list):prog =
	let local_map, next_location = (map_args (Hashtbl.create 8) args next_location) in
	let fn_instr = expr_to_instr body args next_location local_map bad_names in (*turns expr into rubevm code*)
	(Hashtbl.add rube_prog name fn_instr); rube_prog;;

(*Walks over the program - instruction list - and updates the created rubevm program
by delegating to compile_instruction*)
let rec compile_prog_aux (p:simpl_prog) (rube_prog:prog) (bad_names:string list):prog = match p with
	| [] -> rube_prog
	| instruc::tail ->
		let comp_instr = (compile_instruction instruc rube_prog (next_location_func true) bad_names) in
		(compile_prog_aux tail comp_instr bad_names);;

let compile_prog (p:simpl_prog):prog = compile_prog_aux p (Hashtbl.create (List.length p)) (check_bad_names [] p);;

 (*********************************************************************

  (* change this! *)
  let main_instrs =
    [|
      I_const (`L_Reg 0, `L_Str "Fix me!");
      I_ret (`L_Reg 0);
    |]
  in
  let h = Hashtbl.create 17 in
  let _ = Hashtbl.add h "main" main_instrs in
  h

*********************************************************************)

let parse_file name =
  let chan = open_in name in
  let lexbuf = Lexing.from_channel chan in
  let (p:simpl_prog) = Parser.main Lexer.token lexbuf in
    close_in chan;
    p

let main () =
  let p = parse_file Sys.argv.(1) in
  let (p':Instr.prog) = compile_prog p in
  let out_chan = open_out "a.out" in
    disassemble out_chan p'

;;

main ()
