(** Camlp4 syntax extension for execution timing
  	@author Arnaud
  	@since 28-10-06


  Compilation of this syntax extension:
    ocamlc -c \
      -pp 'camlp4o pa_extend.cmo q_MLast.cmo -loc loc' \
      -I +camlp4 pa_timed_enabled.ml
  
  Compilation of a program using this syntax extension:
    ocamlopt -o prog \
      -pp 'camlp4o -I . pa_timed_enabled.cmo' \
      prog.ml


  Description:

	Provides a keyword "timed" which can be used to record the execution
	time of arbitrary OCaml expressions, e.g. function calls.
	Syntax is: [timed expr as id]
	Execution time of [expr] will be recorded under the key [id].
	Using this several times with the same [id] will add up execution times.
	Function [get_all_totals] returns a list of pairs of type [float * t]
	where the first value is the recorded time, and	[t] is the type of [id].
	The construct can be nested.
	To disable the timing functionality, use the extension pa_timed_disabled,
	which will simply expand [timed expr as id] to [expr].
	
	
  Example:

	The following is an example of nested use of the "timed" syntax, to
	measure execution time of calls to a function [fib], whose outputs
	are printed, followed by an output of the total times as returned
	by [get_all_totals].

	let _ = timed (
		print_string (string_of_int (timed (fib 20) as "fib 20") ^ "\n");
		print_string (string_of_int (timed (fib 22) as "fib 22") ^ "\n")
	) as "fib 20 + fib 22" in

	List.iter (fun (time,proc) ->
			Printf.printf "%.5f: %s\n" time proc
	) (get_all_totals ())
	
	
	

*)


(* This inserts the timing functions at the beginning of the source file *)
let insert_timer_functions () =
  let loc = Token.dummy_loc in
  (
  <:str_item<
  	declare
  	
  	value start_timer time_ht s =
  		try (
					let (_,total) = Hashtbl.find time_ht s in
					Hashtbl.replace time_ht s (Sys.time(),total)
  		) with [Not_found -> Hashtbl.add time_ht s (Sys.time(),0.)];

  	value stop_timer time_ht (s:string) =
  		let (run,total) = Hashtbl.find time_ht s in
  		let diff = Sys.time() -. run in
  		Hashtbl.replace time_ht s (diff,total +. diff);

		value get_total time_ht (s:string) =
  		snd (Hashtbl.find time_ht s);

  	value get_all_totals time_ht () =
  		let times = Hashtbl.fold (fun proc (_,time) acc -> [(time,proc)::acc]) time_ht [] in
  		List.sort (fun (time1,_) (time2,_) -> compare time2 time1) times;

  	value time_ht = Hashtbl.create 12;

  	value start_timer = start_timer time_ht;

  	value stop_timer = stop_timer time_ht;

  	value get_all_totals = get_all_totals time_ht;
  	
  	end
	>>,
	loc)

let _ =
  let first = ref true in
  let parse strm =
    let (l, stopped) = Grammar.Entry.parse Pcaml.implem strm in
    let l' = 
      if !first then
        insert_timer_functions () :: l
      else l in
    (l', stopped) in
  Pcaml.parse_implem := parse


(* Returns unique identifiers, needed for nested use *)
let new_id = 
  let counter = ref 0 in
  fun () ->
    incr counter;
    "__timed" ^ string_of_int !counter

(* The function that converts our syntax into a single OCaml expression,
   i.e. an "expr" node of the syntax tree *)
let expand_timed loc e key =
	let id = new_id () in
  <:expr<
  let _ = start_timer $key$
  and $lid:id$ = $e$
  and _ = stop_timer $key$ in
  $lid:id$
  >>
  
(* The statement that extends the default grammar,
   i.e. the regular syntax of OCaml if we use camlp4o 
   or the revised syntax if we use camlp4r *)
EXTEND
  Pcaml.expr: LEVEL "expr1" [
    [ "timed"; e = Pcaml.expr; "as"; key = Pcaml.expr -> expand_timed loc e key ]
  ];
END;;


