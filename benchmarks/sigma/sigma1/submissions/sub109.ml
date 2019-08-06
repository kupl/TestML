(* HW1 exercise2 2009-11697 Kim HyunJoon *)
(* Sigma *)

let rec sigma : int * int * (int -> int) -> int =
	fun (a, b, f) ->
	if a > b then 0
	else if a = b then (f a)
	else (f a) + (sigma ((a+1), b, f))
