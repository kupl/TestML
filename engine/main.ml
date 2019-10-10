open Lang
open Print
open Options
open Preproc

(* Framework for learning functional programming *)
let usage_msg = "main.native -run (or -gentest) -submission <filename> -solution <filename>"

let is_same_type : prog -> prog -> unit
= fun pgm cpgm ->
  let (tenv1, _, _) = Type.run pgm in
  let (tenv2, _, _) = Type.run cpgm in
  let (t1, t2) = (Type.TEnv.find tenv1 !opt_entry_func, Type.TEnv.find tenv2 !opt_entry_func) in
  let _ = Type.unify Type.Subst.empty (t1, t2) in
  ()

(* Run testcases *)
let except_handling : exn -> value -> string
= fun except output ->
  match except with
  |EExcept v -> "Result: " ^ value_to_string v ^ " | " ^ "Expected: " ^ value_to_string output
  |TimeoutError -> "Result: Timeout" ^ " | " ^ "Expected: " ^ value_to_string output
  |Failure s -> "Result: Error " ^ s ^ " | " ^ "Expected: " ^ value_to_string output
  |EqualError -> "Result: Equal Error" ^ " | " ^ "Expected: " ^ value_to_string output
  |_ -> "Result: Evaluation Error " ^ " | " ^ "Expected: " ^ value_to_string output


let run_testcases : prog -> examples -> unit
= fun prog examples ->
  let score = List.fold_left (fun score (inputs, output) ->
    try
      let result_value = Eval.get_output prog inputs in
        print_endline (
          "Input: " ^ input_to_string inputs ^ " | " ^
          "Result: " ^ value_to_string result_value ^ " | " ^  
          "Expected: " ^ value_to_string output
        );
      if try (Eval.value_equality result_value output) with _ -> false then score+1 else score
    with except -> print_endline ("Input: " ^ input_to_string inputs ^ " | " ^ (except_handling except output)); score
  ) 0 examples in
  print_header "Score"; print_endline (string_of_int score)

let run_prog : prog -> examples -> unit
= fun prog examples ->
  let _ = Type.run prog in
  print_header "Program"; print_pgm prog;
  print_header "Run test-cases"; run_testcases prog examples 

let generate_testcases : prog -> prog -> examples
= fun submission solution -> 
  (* type checking *)
  let _ = is_same_type submission solution in
  let _ = print_header "original"; print_pgm submission in
  let test_gen_result = TestGenerator.gen_counter_example submission solution in
  let test_time = Unix.gettimeofday() -. !(TestGenerator.start_time) in 
  match test_gen_result with
  | None -> 
    (* Test-case generation fail *)
    let _ = 
      print_header "Generated examples"; print_endline ("Fail to generate a counter-example");
      print_header "Counter-example time"; print_endline ("Fail to generate a counter-example");
    in
    [] 
  | Some ex ->
    let examples = ex::[] in
    let _ =
      print_header "Generated examples"; print_examples examples;
      print_header "Counter-example time"; print_endline (string_of_float test_time)
    in
    [ex]

let main () = 
  (* Arg Parse *)
  let _ = Arg.parse options (fun s->()) usage_msg in
  let testcases = read_testcases !opt_testcases_filename in
  let solution = read_prog !opt_solution_filename in
  let submission = read_prog !opt_submission_filename in
  let _ = 
    init_pgm := read_external !opt_external_filename;
    grading_pgm := read_external !opt_grading_filename
  in
  (* Main Procedure *)
  if !opt_run then (* Run testcase *)
    begin
      match submission with
      | Some sub -> run_prog sub testcases
      | _ -> raise (Failure (!opt_submission_filename ^ " does not exist"))
    end
  else if !opt_gentest then (* Counter Example Generation *)
    begin
      match submission, solution with
      | Some sub, Some sol -> ignore (generate_testcases sub sol)
      | _ -> raise (Failure "Submission or solution is not provided")
    end
  else Arg.usage options usage_msg


let _ = main ()
