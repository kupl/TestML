(*********************)
(* Problem 1: filter *)
(*********************)
let rec filter pred lst = 
match lst with
| []-> lst
| h::t -> if pred h = true then h::filter pred t else filter pred t

(*********************)
(* Problem 2: zipper *)
(*********************)