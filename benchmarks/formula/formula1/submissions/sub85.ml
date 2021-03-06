type formula = TRUE | FALSE | NOT of formula | ANDALSO of formula * formula | ORELSE of formula * formula | IMPLY of formula * formula | LESS of expr * expr
and expr = NUM of int | PLUS of expr * expr | MINUS of expr * expr



let rec eval f =
	let rec calc _expr =
		match _expr with 
		NUM(_num) -> _num
		| PLUS(_expr1, _expr2) -> (calc _expr1) + (calc _expr2)
		| MINUS(_expr1, _expr2) -> (calc _expr1) - (calc _expr2)
	in

	match f with
	TRUE -> true
	| FALSE -> false
	| NOT x -> not (eval x)
	| ANDALSO(a, b) -> (eval a) && (eval b)
	| ORELSE(a, b) -> (eval a) || (eval b)
	| IMPLY(a, b) -> (not (eval a)) || (eval b)
	| LESS(a, b) -> (calc a) < (calc b)
