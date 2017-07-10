(** Camlp4 syntax extension for execution timing
  	@author Arnaud
  	@since 28-10-06

	See pa_timed_enabled.ml for documentation.
*)


(* get_all_totals should be defined, but it always returns the empty list *)
let insert_timer_functions () =
  let loc = Token.dummy_loc in
  (
  <:str_item<
  	declare
  	
  	value get_all_totals () = [];
  	
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

(* The statement that extends the default grammar,
   i.e. the regular syntax of OCaml if we use camlp4o 
   or the revised syntax if we use camlp4r *)
EXTEND
  Pcaml.expr: LEVEL "expr1" [
    [ "timed"; e = Pcaml.expr; "as"; key = Pcaml.expr -> e ]
  ];
END;;


