open Ast

module Env : sig
	type t

	val empty : t

	val add_var : t -> Ast.var -> tp -> t
	val add_vars : t -> (Ast.var * tp) list -> t

	val lookup_var : t -> Ast.var -> tp option
end = struct
	module StrMap = Map.Make(String)

	type t = tp StrMap.t

	let empty = StrMap.empty

	let add_var env x tp =
		StrMap.add x tp env

	let add_vars =
		List.fold_left (fun env (x, tp) -> add_var env x tp)

	let lookup_var env x =
		StrMap.find_opt x env
end

exception Type_error

let rec nth_of_list xs n =
	if n < 0
		then None
		else 
		(match xs, n with 
		| [], _ -> None 
		| x :: xs', 0 -> Some x
		| x :: xs', _ -> nth_of_list xs' (n - 1)
		)

let rec contains_arrow (t : Ast.tp) = 
	match t with
	| TArrow _ -> raise Type_error
	| TTuple tlist -> (List.iter contains_arrow tlist; ())
	| _ -> ()
(* do sprawdzania czy nie używa się funkcji ukrytej w krotkach w miejscach niedozwolonych (wartość zwracana przez funkcje / porównania)*)

let rec infer_type env (prog : Ast.expr) (fun_h : Ast.tp list) =

	let use_infer env (e : Ast.expr) = 
		infer_type env e fun_h in 
	let use_check env (e : Ast.expr) tp = 
		check_type env e tp fun_h
	in
	(* funkcje mające umożliwić skrótowy zapis by fragmenty kodu które nie dotykają zagnieżdżonych funkcji nie musiały przejmować się obsługą fun_h *)
	match prog with 

		| Var  v -> 
			begin 
				match Env.lookup_var env v with
				| Some t -> t
				| None -> raise Type_error
			end

		| Int _ -> TInt

		| Bool _ -> TBool

		| Binop (op, e1, e2) ->  
			use_check env e1 TInt;
			use_check env e2 TInt;
			TInt

		| Cmpop (op, e1, e2) -> 
			let tp1 = use_infer env e1 in
			use_check env e2 tp1;
			contains_arrow tp1;
			TBool

		| Let (x, e1, e2) ->
			let tpv = use_infer env e1 in 
			use_infer (Env.add_var env x tpv) e2


		| If (e1, e2, e3) -> 
			use_check env e1 TBool;
			let tp2 = use_infer env e2 in 
			use_check env e3 tp2;
			tp2 

		| Tuple elist -> 
			let tlist = List.map (use_infer env) elist in 
			TTuple tlist 

		| Select (e1, i) -> 
			begin 
				match use_infer env e1 with
				| TTuple elist -> 
					(match nth_of_list elist i with 
					| Some t -> t
					| None -> raise Type_error)
				| _ -> raise Type_error
			end

		| FunRec (xf, xtl, tpf, body) -> 
			contains_arrow tpf;
			let new_env = Env.add_vars env xtl in 
			let t = TArrow( List.map snd xtl , tpf) in 
			check_type (Env.add_var new_env xf t) body tpf (tpf :: fun_h);
			t		

		| App (ef, elist) -> 
			begin 
				match use_infer env ef with 
				| TArrow (argt, tf) -> 
					if List.length elist = List.length argt 
						then (List.iter2 (use_check env) elist argt; tf )
						else raise Type_error 
				| _ -> raise Type_error
			end 

		| Read (x, e) -> use_infer (Env.add_var env x TInt) e

		| Write (e1, e2) -> 
			use_check env e1 TInt;
			use_infer env e2

		| Return (i, e, tp) -> 
			let type_r = use_infer env e in 
			begin 
				match nth_of_list fun_h i with
					| Some t -> (if t = type_r 
						then tp
						else raise Type_error)
					| None -> raise Type_error
			end 
and check_type env (prog : Ast.expr) (t : Ast.tp) fun_h = 
	if infer_type env prog fun_h <> t 
		then raise Type_error
	
let check_program prog : unit =
	check_type Env.empty prog TInt [TInt]
(* fun_h jest zainicjalizowane jako [TInt] co reprezentuje typ który jest oczekiwany by cały program zwrócił *)