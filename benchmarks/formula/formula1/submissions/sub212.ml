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

let rec calc ex =
 match ex with
 | NUM n -> n 
 | PLUS(n1,n2) -> calc n1 + calc n2 
 | MINUS(n1,n2) -> calc n1 - calc n2

let rec eval f=
 match f with
 | TRUE -> true
 | FALSE -> false
 | NOT f1 -> if eval f1= true then false else true
 | ANDALSO(f1,f2) -> if eval f1 = true then eval f2 else false
 | ORELSE(f1,f2) -> if eval f1 = false then eval f2 else true
 | IMPLY(f1,f2) -> if eval f1 = true then eval f2 else true 
 | LESS(e1,e2) -> if calc e1 < calc e2 then true else false