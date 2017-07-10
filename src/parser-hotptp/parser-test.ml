
open Hol_type
open Term
open Signature
open List


let _ =
  let lexbuf = Lexing.from_channel stdin in
  let (termlist,sigma,_) = Htparser.input Htlexer.token lexbuf in
    let _ = print_string "\ntype variables:\n" in
    let _ = iter print_endline (all_type_vars sigma) in

    let _ = print_string "\nuninterpreted terms:\n" in
		let _ = iter (fun (s,ty) ->
			print_string (s^": "^(Hol_type.to_hotptp ty)^"\n")) (all_uninterpreted_symbols sigma) in
    
    let _ = print_string "\ndefined terms:\n" in
    let _ = iter (fun (s,(t,ty)) ->
      print_string (s^": "^(Term.to_hotptp t)^"\n")) (all_defined_symbols sigma) in
      
    let _ = print_string "\ncreated terms:\n" in
    let _ = iter (fun t -> print_string ((Term.to_hotptp t)^"\n")) termlist in
    flush stdout

            
