exception Error of string
type formula = TRUE
	| FALSE
	| NOT of formula
	| ANDALSO of formula * formula
	| ORELSE of formula * formula
	| IMPLY of formula * formula
	| LESS of expr * expr
and expr = NUM of int
		 | PLUS of expr * expr
		 | MINUS of expr * expr


let rec eval f = 
	match f with
		TRUE -> true
		| FALSE -> false
		| NOT f -> not(eval f)
		| ANDALSO (f1, f2) -> (eval f1) && (eval f2)
		| ORELSE (f1, f2) -> (eval f1) || (eval f2)
		| IMPLY (f1, f2) -> (not(eval f1)) || (eval f2)
		| LESS (e1, e2) ->
			let rec expr_to_num e =
				match e with
				NUM n -> n
				| PLUS (e1, e2) -> (expr_to_num e1) + (expr_to_num e2)
				| MINUS (e1, e2) -> (expr_to_num e1) - (expr_to_num e2)
			in
				if( (expr_to_num e1) < (expr_to_num e2)) then true
				else
					false
	
;;


	
