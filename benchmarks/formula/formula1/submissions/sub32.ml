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

let rec eval : formula  -> bool =
  fun f ->
    let rec ex : expr -> int =
      fun e -> match e
      with NUM(i) -> i
        | PLUS(e1,e2) -> ex(e1)+ex(e2)
        | MINUS(e1,e2) -> ex(e1)-ex(e2)
    in
        match f
        with TRUE -> true
          | FALSE -> false
          | NOT(f) -> not (eval f)
          | ANDALSO(f1,f2) -> (eval f1) && (eval f2)
          | ORELSE(f1,f2) -> (eval f1) || (eval f2)
          | IMPLY(f1,f2) -> (not (eval f1)) || (eval f2)
          | LESS(e1,e2) -> (ex e1)<(ex e2)
