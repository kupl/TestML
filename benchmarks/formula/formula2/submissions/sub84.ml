type formula =
	| True
	| False 
	| Not of formula 
	| AndAlso of formula * formula 
	| OrElse of formula * formula 
	| Imply of formula * formula 
	| Equal of exp * exp

and exp = 
	| Num of int 
	| Plus of exp * exp 
	| Minus of exp * exp 

let rec eval : formula -> bool
= let rec expcall : exp -> int = fun e -> match e with Num(x) -> x | Plus(x, y) -> (expcall(x)) + (expcall(y)) | Minus(x, y) -> (expcall(x)) - (expcall(y)) in fun f -> match f with True -> true | False -> false | Not(x) -> not (eval(x)) | AndAlso(x, y) -> (eval(x))&&(eval(y)) | OrElse(x, y) -> (eval(x))||(eval(y)) | Imply(x, y) -> if (eval(x)) == true && (eval(y)) == false then false else true | Equal(x, y) -> if (expcall(x)) == (expcall(y)) then true else false;;

