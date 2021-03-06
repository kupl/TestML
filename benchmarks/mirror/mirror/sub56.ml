(* problem 1*)
type btree = Empty | Node of int * btree * btree

let rec mirror : btree -> btree
= fun t -> (* TODO *)
  match t with
    | Empty -> Empty
    | Node(key, lb, rb) -> Node(key, mirror rb, mirror lb)