(* School of Computer Science & Engineering
 * 2009-23151
 * 조성근
 * HW 1 - Exercise 2
 *)

let rec iter (n, f) a = 
  if n=0 then a
  else f ((iter (n-1,f)) a);;
