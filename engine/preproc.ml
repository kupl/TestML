open Lang 

(* Read program from file *)
let preprocess_file : string -> string
= fun filename -> 
  let ic = open_in filename in
  let lines = ref [] in
  begin try
    while true do
      lines := (input_line ic)::!lines
    done
  with End_of_file -> 
    close_in ic
  end;
  List.rev !lines |> String.concat "\n"

let parse_file : string -> examples * prog
= fun f -> 
  try 
    preprocess_file f
    |> Lexing.from_string
    |> Parser.prog Lexer.token
  with _ -> raise (Failure ("Parsing error : " ^ f))

let read_prog : string -> prog option
= fun filename -> if Sys.file_exists filename then Some (snd (parse_file filename)) else None 

(* Read testcases *)
let read_testcases : string -> examples
= fun file_name ->
  if file_name = "" then [] 
  else 
    try fst (parse_file file_name) 
    with e -> raise e

(* Read external library *)
let read_external : string -> prog 
= fun filename -> if Sys.file_exists filename then snd (parse_file filename) else []