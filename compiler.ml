open Ast
open Instr
open Disassembler


(*********************************************************************)

(*
  Increments its output by 1 starting at 0 when flag is true. If flag is
  false, then the rcount is reset to 0.
*)
let next_location_func flag =
  let x = ref (-1) in (
  fun () ->
    if flag then
      (x := !x + 1; !x)
    else
      (x := 0; !x)
  )
;;

(*
  Takes a return instruction and returns the register to be returned
*)
let get_register_value = function
  | I_ret r -> r
  | _ -> failwith "coding error: expected return instruction";;

let eval_expression_and

let rec expr_to_instr (body:expr) (args:string list) (next_location:(unit -> int))
(local_map:((string, int) Hashtbl.t)) (bad_names:string list):fn =

  match body with

  (* Create an integer *))
  | EInt n ->
		let loc = next_location () in (*get register location*)
		let inst1 = I_const ((`L_Reg loc), (`L_Int n)) in (*load n into register*)
		let inst2 = I_ret (`L_Reg loc) in  (*create return register with n*)
    [|instr1; instr2|] (*create and return instruction array*)

  (* Create a string *)
	| EString str ->
		let loc = next_location () in (*get register location*)
		let inst1 = I_const ((`L_Reg loc), (`L_Str str)) in (*load str into register*)
		let inst2 = I_ret (`L_Reg loc) in  (*create return register with str*)
		[|instr1; instr2|] (*create and return instruction array*)

  (* Attempt to read a local variable *)
	| ELocRd id ->
    (*
      checks if id has been mapped to a register in the function call, if so
		  then creates a return instruction with the mapped register; else, creates a
      return to a non-existant register.
    *)
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

  (* Write a value to a variable *)
	| ELocWr (id, expr) ->

		(* Build code for expr and the value *)
		let instr_for_expr, expr_value = evaluate_expression expr args next_location local_map bad_names in

		let loc = if Hashtbl.mem local_map id then Hashtbl.find local_map id else next_location () in 
		let inst1 = I_mov ((`L_Reg loc), expr_value) in (* copy the expr's value into new register *)
		let inst2 = I_ret (`L_Reg loc) in (* return the value of the local variable *)
		Array.append instr_for_expr ([|inst1;inst2|]) (* Combine the instructions *)


  (* 
  	If statement 
			if exp1 then exp2 else exp3
  *)
	| EIf (exp1, exp2, exp3) ->
		(* Build code for exp1 and the value*)
		let instr_for_exp1, exp1_value = evaluate_expression exp1 args next_location local_map bad_names in
		(* Build code for exp2 and exp3 *)
		let instr_for_exp2 = (expr_to_instr exp2 args next_location local_map bad_names) in
		let instr_for_exp3 = (expr_to_instr exp3 args next_location local_map bad_names) in

		(*if exp1 = 0 jump past code of exp2 - see how code is organized below*)
		let inst = I_if_zero (exp1_value, (Array.length instr_for_exp2)) in

		(*code_of_v1 + [|inst1|] + code_of_v2 + code_of_v3 *)
		let instrucs = Array.append instr_for_expr1 ([|inst|]) in
		let instrucs = Array.append instrucs instr_for_exp2 in
		let instrucs = Array.append instrucs instr_for_exp3 in
		instrucs

	(* 
		While loop 
			while exp1, compute block exp2
	*)
	| EWhile (exp1, exp2) ->
		(* Build code for exp1 and the value*)
		let instr_for_exp1, exp1_value = evaluate_expression exp1 args next_location local_map bad_names in
		(* Build the code for exp2 - remove the return instr *)
		let instr_for_exp2, _ = evaluate_expression exp1 args next_location local_map bad_names in
		
		let length_of_exp1_instr = Array.length instr_for_exp1 in
		let length_of_exp2_instr = Array.length instr_for_exp2 in 

		(* if exp1 = 0 then jump past code of exp2 - see how code is organized below *)
		let inst1 = I_if_zero (exp1_value, (length_of_exp2_instr + 1) in

		(* Jump back to the top of the while loop *)
		let inst2 = I_jmp (-1 * (2 + length_of_exp2_instr + length_of_exp1_instr) in
		let inst3 = I_ret (exp1_value) in (* Create the return from the while loop*)

		(* put it all together *)
		let instrucs = Array.append instr_for_exp1 ([|inst1|]) in
		let instrucs = Array.append instrucs instr_for_exp2 in
		Array.append instrucs ([|inst2;inst3|]) in

	(* Compute expr1, then exp2 *)
	| ESeq (exp1, exp2) ->
		(* 
			Build the code for exp1 - remove the return instr 
			Build the code for exp2
			put it together
		*)
		let instr_for_exp1, _ = evaluate_expression exp1 args next_location local_map bad_names in
		let instr_for_exp2 = expr_to_instr exp2 args next_location local_map bad_names in
		Array.append instr_for_exp1 instr_for_exp2

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
			This is code to throw a readable error in the event the program
			is attempting to pass non-integers to the binary operator.
			You should get this added into the compiler!

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


and let evaluate_expression expr args next_location local_map bad_names =
  let code_for_expr = (expr_to_instr expr args next_location local_map bad_names) in (*generate instrucs*)
  let return_position = (Array.length code_for_expr) - 1 in
  let return_register = Array.get code_for_expr return_position in (*get return inst*)
  let return_value = get_register_value return_register in (*get the register*)
  let code_for_expr = Array.sub code_for_expr 0 return_position in (*remove return inst*)
  (code_for_expr, return_value)
;;


(*
  Places the ids into the given table.
  @param [Hashtbl] tbl - The table to place the ids in
  @param [string list] ids - The ids to place in the table
  @param [unit -> int] next_location - The function for generating the location to
    map an id to within the table.
*)
let rec map_args (tbl:((string, int) Hashtbl.t)) (ids:string list) (next_location:(unit -> int)) =
	match ids with
  | [] ->
    tbl, next_location
  | id::tail ->
    (Hashtbl.replace tbl id (next_location ()));
    map_args tbl tail next_location
;;

(*
  Moves through the program and identifies all 'bad' function names.
*)
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

(*
  Creates a new entry in the rubevm program for the incoming function
*)
let compile_instruction ({fn_name=name; fn_args=args; fn_body=body}:simpl_fn)
(rube_prog:prog) (next_location:(unit -> int)) (bad_names:string list):prog =

	let local_map, next_location = (map_args (Hashtbl.create 8) args next_location) in
	let fn_instr = expr_to_instr body args next_location local_map bad_names in (*turns expr into rubevm code*)
  (Hashtbl.add rube_prog name fn_instr); rube_prog
;;

(*
  Walks over the program - instruction list - and updates the created rubevm program
  by delegating to compile_instruction
*)
let rec compile_prog_aux (p:simpl_prog) (rube_prog:prog) (bad_names:string list):prog =
  match p with
	| [] -> rube_prog
	| instruc::tail ->
		let comp_instr = (compile_instruction instruc rube_prog (next_location_func true) bad_names) in
    (compile_prog_aux tail comp_instr bad_names)
;;


(*
  Compiles a emerarld program into emeraldbyte code.
*)
let compile_prog (p:simpl_prog):prog =
  compile_prog_aux p (Hashtbl.create (List.length p)) (check_bad_names [] p)
;;