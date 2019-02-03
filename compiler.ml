open Ast
open Instr
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
  | _ -> failwith "coding error: expected return instruction"
;;

(* Checks function definition and argument count errors *)
let check_function_name_and_arguments function_name count_map exp_list =

	(* Check that the function exists *)
	if not (Hashtbl.mem count_map function_name) then 
		failwith ("Function - " ^ function_name ^ " - is not defined")
	else ();

	let arg_count = Hashtbl.find count_map function_name in 
	let exp_count = List.length exp_list in 

	if exp_count < arg_count then 
		failwith (
			"Missing argument(s), function - " ^ function_name ^ " - requires " ^ (string_of_int arg_count) ^ 
			" argument(s), but only " ^ (string_of_int exp_count) ^ " arguments were provided"
		)
	else if (exp_count > arg_count) then  
		failwith (
			"Too many arguments, function - " ^ function_name ^ " - requires " ^ (string_of_int arg_count) ^ 
			" argument(s), but " ^ (string_of_int exp_count) ^ " arguments were provided"
		)
	else ()
;;

let rec expr_to_instr (body:expr) (count_map) (next_location:(unit -> int))
(local_map:((string, int) Hashtbl.t)) (function_names:string list):fn =
	
  match body with

  (* Create an integer *)
  | EInt n ->
		let r1 = `L_Reg (next_location ()) in
    [|
    	I_const (r1, (`L_Int n));
    	I_ret r1
    |]

  (* Create a string *)
	| EString str ->
		let r1 = `L_Reg (next_location ()) in
    [|
    	I_const (r1, (`L_Str str));
    	I_ret r1
    |]

  (* Attempt to read a local variable *)
	| ELocRd id ->
    (*
      checks if id has been mapped to a register in the function call, if so
		  then creates a return instruction with the mapped register; else, creates a
      return to a non-existant register.
    *)
		if (Hashtbl.mem local_map id) then  (*id has a mapping*)
			let loc = (Hashtbl.find local_map id) in (*get register value*)
			[|
				I_ret (`L_Reg loc)
			|]
		else
			failwith ("Variable - " ^ id ^ " - is not bound in this environment.")

  (* Write a value to a variable *)
	| ELocWr (id, expr) ->

		(* Build code for expr and the value *)
		let instr_for_expr, expr_value = evaluate_expression expr count_map next_location local_map function_names in

		let loc = if Hashtbl.mem local_map id then Hashtbl.find local_map id else next_location () in
		Hashtbl.replace local_map id loc;

		let r1 = `L_Reg loc in
		Array.append instr_for_expr
		[|
			I_mov (r1, expr_value);
			I_ret r1
		|]


  (*
  	If statement
			if exp1 then exp2 else exp3
  *)
	| EIf (exp1, exp2, exp3) ->
		(* Build code for exp1 and the value*)
		let instr_for_exp1, exp1_value = evaluate_expression exp1 count_map next_location local_map function_names in
		(* Build code for exp2 and exp3 *)
		let instr_for_exp2 = (expr_to_instr exp2 count_map next_location local_map function_names) in
		let instr_for_exp3 = (expr_to_instr exp3 count_map next_location local_map function_names) in

		(*if exp1 = 0 jump past code of exp2 - see how code is organized below*)
		let inst = I_if_zero (exp1_value, (Array.length instr_for_exp2)) in

		(*code_of_v1 + [|inst1|] + code_of_v2 + code_of_v3 *)
		let instrucs = Array.append instr_for_exp1 ([|inst|]) in
		let instrucs = Array.append instrucs instr_for_exp2 in
		Array.append instrucs instr_for_exp3

	(*
		While loop
			while exp1, compute block exp2
	*)
	| EWhile (exp1, exp2) ->
		(* Build code for exp1 and the value*)
		let instr_for_exp1, exp1_value = evaluate_expression exp1 count_map next_location local_map function_names in
		(* Build the code for exp2 - remove the return instr *)
		let instr_for_exp2, _ = evaluate_expression exp2 count_map next_location local_map function_names in

		let length_of_exp1_instr = Array.length instr_for_exp1 in
		let length_of_exp2_instr = Array.length instr_for_exp2 in

		(* put it all together *)
		let instrucs = Array.append instr_for_exp1 [|I_if_zero (exp1_value, (length_of_exp2_instr + 1))|] in
		let instrucs = Array.append instrucs instr_for_exp2 in
		Array.append instrucs
		[|
			(* Jump back to the top of the while loop *)
			I_jmp (-1 * (2 + length_of_exp2_instr + length_of_exp1_instr));
			I_ret (exp1_value)
		|]


	(* Compute expr1, then exp2 *)
	| ESeq (exp1, exp2) ->
		(*
			Build the code for exp1 - remove the return instr
			Build the code for exp2
			put it together
		*)
		let instr_for_exp1, _ = evaluate_expression exp1 count_map next_location local_map function_names in
		let instr_for_exp2 = expr_to_instr exp2 count_map next_location local_map function_names in
		Array.append instr_for_exp1 instr_for_exp2

	| EBinOp (exp1, op, exp2) ->
		binary_expr_to_instr exp1 exp2 op count_map next_location local_map function_names

	| ETabRd (exp1, exp2) ->

		let instr_for_exp1, exp1_value = evaluate_expression exp1 count_map next_location local_map function_names in
		let instr_for_exp2, exp2_value = evaluate_expression exp2 count_map next_location local_map function_names in
		let r1 = `L_Reg (next_location ())  in
		let r2 = `L_Reg (next_location ()) in
		let error_message1 = `L_Str "Error: Invalid input on table read - first argument must be a table" in
		let error_message2 = `L_Str "Error: Invalid input on table read - key does not exist" in

		Array.append (Array.append instr_for_exp1 instr_for_exp2)
		[|
			I_const (r2, (`L_Int 1));

			(* Check that the exp1 is a table *)
			I_is_tab (r1, exp1_value);
			I_sub (r1, r1, r2);
			I_if_zero (r1, 2);

			(* Error if no table *)
			I_const (r1, error_message1);
			I_halt r1;

			(* Check that the table key exists *)
			I_has_tab (r1, exp1_value, exp2_value);
			I_sub (r1, r1, r2);
			I_if_zero (r1, 2);
			
			(* Error if key doesn't exist *)
			I_const (r1, error_message2);
			I_halt r1;
			
			(* Read from the table *)
			I_rd_tab (r1, exp1_value, exp2_value);
			I_ret r1
		|]

	| ETabWr (exp1, exp2, exp3) ->
		(* Evaluate the expressions *)
		let instr_for_exp1, exp1_value = evaluate_expression exp1 count_map next_location local_map function_names in
		let instr_for_exp2, exp2_value = evaluate_expression exp2 count_map next_location local_map function_names in
		let instr_for_exp3, exp3_value = evaluate_expression exp3 count_map next_location local_map function_names in
		let exp_instr = Array.append (Array.append instr_for_exp1 instr_for_exp2) instr_for_exp3 in
		
		let r1 = `L_Reg (next_location ())  in
		let r2 = `L_Reg (next_location ()) in
		let error_message = `L_Str "Error: Invalid input on table read - first argument must be a table" in

		Array.append exp_instr
		[|
			(* Check that the exp1 is a table *)
			I_const (r2, (`L_Int 1));
			I_is_tab (r1, exp1_value);
			I_sub (r1, r1, r2);
			I_if_zero (r1, 2);

			(* Error if no table *)
			I_const (r1, error_message);
			I_halt r1;

			I_wr_tab (exp1_value, exp2_value, exp3_value);
			I_ret(exp3_value)
		|]

	| ECall (function_name, exp_list) ->
		call_to_instr function_name exp_list count_map next_location local_map function_names

(*
	Creates instructions for evaluating an expression. Automatically strips
	the return statement from the instructions, and extracts the register from it.
	Returns a tuple of the instructions and the register that was to be returned.

	@return [(instr array, reg)] Tuple of instructions and return register
*)
and evaluate_expression expr count_map next_location local_map function_names =
	(* generate instrucs for expression *)
  let code_for_expr = (expr_to_instr expr count_map next_location local_map function_names) in 
  
  (* get return register *)
  let return_position = (Array.length code_for_expr) - 1 in
  let return_register = Array.get code_for_expr return_position in 
  let return_value = get_register_value return_register in 
  
  (* remove return instruction *)
  let code_for_expr = Array.sub code_for_expr 0 return_position in 
  (* instructions, return register *)
  (code_for_expr, return_value)

(*
	Creates the instructions for a EBinOp
*)
and binary_expr_to_instr exp1 exp2 op count_map next_location local_map function_names =
	
	(* Evaluate the expressions *)
	let instr_for_exp1, exp1_value = evaluate_expression exp1 count_map next_location local_map function_names in
	let instr_for_exp2, exp2_value = evaluate_expression exp2 count_map next_location local_map function_names in
	let instrucs = Array.append instr_for_exp1 instr_for_exp2 in 
	
	(* Determine binary operator instruction *)
	let return_reg = `L_Reg (next_location ()) in
	let binary_op_instr = (
		match op with
		| BPlus -> I_add(return_reg, exp1_value, exp2_value)
		| BMinus -> I_sub(return_reg, exp1_value, exp2_value)
		| BTimes -> I_mul(return_reg, exp1_value, exp2_value)
		| BDiv -> I_div(return_reg, exp1_value, exp2_value)
		| BLt -> I_lt(return_reg, exp1_value, exp2_value)
		| BLeq -> I_leq(return_reg, exp1_value, exp2_value)
		| BEq -> I_eq(return_reg, exp1_value, exp2_value)
	) in
	
	(* Registers for checking args are ints *)
	let exp_check_reg = `L_Reg (next_location ()) in
  let sub_reg = `L_Reg (next_location ()) in 
  
  Array.append instrucs 
  [|
  	I_const (sub_reg, `L_Int 1);

  	(* Check that exp1 is an int *)
    I_is_int (exp_check_reg, exp1_value);
    I_sub(exp_check_reg, exp_check_reg, sub_reg);
    I_if_zero (exp_check_reg, 2);
    I_const (exp_check_reg, (`L_Str "Illegal argument (1) passed to binary operator. Arguments must be integers"));
    I_halt exp_check_reg;
    
    (* Check that exp2 is an int *)
    I_is_int (exp_check_reg, exp2_value);
    I_sub(exp_check_reg, exp_check_reg, sub_reg);
    I_if_zero (exp_check_reg, 2);
    I_const (exp_check_reg, (`L_Str "Illegal argument (2) passed to binary operator. Arguments must be integers"));
    I_halt exp_check_reg;

    (* Run the binary op *)
		binary_op_instr;
    I_ret return_reg
  |]

(*
	Creates the instructions for an ECall 
*)
and call_to_instr function_name exp_list count_map next_location local_map function_names =

	(* Check that the number of supplied args *)
	check_function_name_and_arguments function_name count_map exp_list;

	if (List.mem function_name function_names) then (
		(*
			This is a call to a user defined function.
		*)

		(* Create the instructions for evaluating the arguments to the call *)
		let instrucs, regs = List.fold_left (
			fun (instrucs,regs) exp ->

				let instr_for_exp, exp_value = evaluate_expression exp count_map next_location local_map function_names in
				let instrucs = Array.append instrucs instr_for_exp in
				let regs = regs@[exp_value] in
				
				(instrucs, regs)

			) ([||],[]) exp_list in

			(* Instructions for copying all the argument expressions into new registers *)
			let instrucs = List.fold_left (
				fun instrucs reg_value ->
					
					let loc = next_location () in
					Array.append instrucs [|I_mov ((`L_Reg loc), reg_value)|]

			) instrucs regs in

			(* Create function name register *)
			let r1_loc = next_location () in
			let r1 = `L_Reg r1_loc in

			(* Determine the locations of the argument registers *)
			let call_start = r1_loc - (List.length regs) in
			let call_end = r1_loc - 1 in
			
			Array.append instrucs
			[|
				I_const (r1, (`L_Id function_name));
				I_call (r1, call_start, call_end);
				I_ret (`L_Reg call_start)
			|]

	) else ( (* This is a built in call *)
		built_in_call_to_instr function_name exp_list count_map next_location local_map function_names
	)

(*
	Creates the instructions for a built in function.
	Note: This also handles the error of calling an undefined function.
*)
and built_in_call_to_instr function_name exp_list count_map next_location local_map function_names =

	if function_name = "mktab" then (
			let r1 = `L_Reg (next_location ()) in
			[| I_mk_tab r1; I_ret r1 |]
	) else (
		(* Instructions for is_i, is_s, and is_t *)
		let exp::_ = exp_list in
		let instr_for_exp, exp_value = evaluate_expression exp count_map next_location local_map function_names in
		let r1 = `L_Reg (next_location ()) in

		let is_instr = (
			match function_name with
				| "is_i" -> I_is_int (r1, exp_value)
				| "is_s" -> I_is_str (r1, exp_value)
				| "is_t" -> I_is_tab (r1, exp_value)
				| _ -> failwith ("Function - " ^ function_name ^ " - is not defined")
		) in

		Array.append instr_for_exp
		[|
			is_instr;
			I_ret r1
		|]
	)
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
	Maps the functions in the program by their name to their argument counts. Storing the
	result in count_map.
*)
let rec create_function_args_count_map (p:simpl_prog) count_map function_names = 
	match p with 
	 | [] -> 
	 		(* Add the arg counts for all the built in functions *)
	 		if not (List.mem "to_s" function_names) then Hashtbl.replace count_map "to_s" 1 else ();
	 		if not (List.mem "to_i" function_names) then Hashtbl.replace count_map "to_i" 1 else ();
	 		if not (List.mem "concat" function_names) then Hashtbl.replace count_map "concat" 2 else ();
	 		if not (List.mem "print_string" function_names) then Hashtbl.replace count_map "print_string" 1 else ();
	 		if not (List.mem "print_int" function_names) then Hashtbl.replace count_map "print_int" 1 else ();
	 		if not (List.mem "size" function_names) then Hashtbl.replace count_map "size" 1 else ();
	 		if not (List.mem "length" function_names) then Hashtbl.replace count_map "length" 1 else ();
	 		if not (List.mem "is_s" function_names) then Hashtbl.replace count_map "is_s" 1 else ();
	 		if not (List.mem "is_i" function_names) then Hashtbl.replace count_map "is_i" 1 else ();
	 		if not (List.mem "is_t" function_names) then Hashtbl.replace count_map "is_t" 1 else ();
	 		if not (List.mem "mktab" function_names) then Hashtbl.replace count_map "mktab" 0 else ();
	 		(* Return the updated table *)
	 		count_map

	 | head::tail -> 
	 		(* Add the arg count of the current function *)
	 		Hashtbl.replace count_map (head.fn_name) (List.length (head.fn_args));
	 		create_function_args_count_map tail count_map function_names
;;

(*
  Moves through the program and identifies all 'bad' function names.
*)
let rec extract_function_names (function_names:(string list)) (p:simpl_prog):(string list) =
	match p with
	| [] -> function_names
	| head::tail -> extract_function_names ((head.fn_name)::function_names) tail

(*
  Creates a new entry in the rubevm program for the incoming function
*)
let compile_instruction ({fn_name=name; fn_args=args; fn_body=body}:simpl_fn)
(evm_prog:prog) (next_location:(unit -> int)) (function_names:string list) (count_map):prog =

	let local_map, next_location = (map_args (Hashtbl.create 8) args next_location) in

	(*turns expr into rubevm code*)
	let fn_instr = expr_to_instr body count_map next_location local_map function_names in 
  
  (Hashtbl.add evm_prog name fn_instr);
  evm_prog
;;

(*
  Walks over the program - instruction list - and updates the created rubevm program
  by delegating to compile_instruction
*)
let rec compile_prog_aux (p:simpl_prog) (evm_prog:prog) (function_names:string list) (count_map):prog =
  match p with
	| [] -> evm_prog
	| instruc::tail ->
		let comp_instr = compile_instruction instruc evm_prog (next_location_func true) function_names count_map in
    (compile_prog_aux tail comp_instr function_names count_map)
;;


(*
  Compiles a emerarld program into emeraldbyte code.
*)
let compile_prog (p:simpl_prog):prog =
	(* Will store the resulting EmeraldVM *)
	let evm_prog = Hashtbl.create (List.length p) in 

	(* Get the user defined function names *)
	let function_names = extract_function_names [] p in 

	(* 
		Create a map from funciton name to number of arguments for 
		determining incorrect argument exceptions
	 *)
	let count_map = create_function_args_count_map p (Hashtbl.create (List.length p)) function_names in 

	(* Add the prebuilt functions from EmeraldVM into viable function names *)
	let function_names = function_names@["to_s";"to_i";"concat";"print_string";"print_int";"size";"length"] in 
  
	(* Compile the program *)
  compile_prog_aux p evm_prog function_names count_map
;;



