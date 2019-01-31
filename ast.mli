type bop =
  | BPlus
  | BMinus
  | BTimes
  | BDiv
  | BEq
  | BLt
  | BLeq

type expr =
  | EInt of int
  | EString of string
  | ELocRd of string    (* Read a local variable *)
  | ELocWr of string * expr  (* Write a local variable *)
  | EIf of expr * expr * expr
  | EWhile of expr * expr
  | ESeq of expr * expr
  | EBinOp of expr * bop * expr
  | ETabRd of expr * expr
  | ETabWr of expr * expr * expr
  | ECall of string * (expr list)

(*  name * arg list * body *)
type simpl_fn = {
  fn_name : string;
	fn_args : string list;
  fn_body : expr
}

(* program is a list of functions *)
type simpl_prog = simpl_fn list
