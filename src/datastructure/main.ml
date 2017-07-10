open List
open Util
open Term
open Termset
open Termsystem
open Signature
open Literal
open Clause
open Clauseset
open Hol_type
open State

(*FIXME using exceptions for encoding control flow
        is not ideal, but these exceptions make
        explicit the signals which were previously
        encoded in generic "Failure" exceptions.*)
exception EMPTYCLAUSE_DERIVED
exception MAX_CLAUSES
exception MAX_LOOPS
exception ACTIVE_EMPTY

(** The weight functions for literals and clauses (temporary) *)

let rec lit_compute_weight (l:role xterm) = 1 (* not implemented yet *)
(*
  match l with
    Symbol t -> 1
  | Appl (t1,t2) ->  (lit_compute_weight t1) +  (lit_compute_weight t1)
  | Abstr (t1,ty,t2) ->  1 + (lit_compute_weight t2)
*)

(* finding and removing clauses *)

let find_clause_by_number (st:state) (i:int) =
  (* maybe active and passive should be hashtables ? *)
  let cl1 = Set_of_clauses.filter (fun c -> c.cl_number = i) st.active in
  if Set_of_clauses.is_empty cl1 then
    let cl2 = Set_of_clauses.filter (fun c -> c.cl_number = i) st.passive in
    if Set_of_clauses.is_empty cl2 then raise (Failure "Not found") else
    Set_of_clauses.choose cl2
  else Set_of_clauses.choose cl1

let find_and_remove_clause_by_number (st:state) (i:int) =
  let cl1 = Set_of_clauses.filter (fun c -> c.cl_number = i) st.active in
  if Set_of_clauses.is_empty cl1 then
    let cl2 = Set_of_clauses.filter (fun c -> c.cl_number = i) st.passive in
    if Set_of_clauses.is_empty cl2 then raise (Failure "Not found") else
    let c2 = Set_of_clauses.choose cl2 in remove_from_passive st c2; c2
  else let c1 = Set_of_clauses.choose cl1 in remove_from_active st c1; c1

let find_and_remove_clause_by_number_in_active (st:state) (i:int) =
  let (is_in_list,is_not_in_list) = Set_of_clauses.partition (fun c -> c.cl_number = i) st.active
  in 
  if Set_of_clauses.is_empty is_in_list then raise (Failure "Not found") else
  (set_active st is_not_in_list; Set_of_clauses.choose is_in_list)

let find_and_remove_clause_by_number_in_passive (st:state) (i:int) =
  let (is_in_list,is_not_in_list) = Set_of_clauses.partition (fun c -> c.cl_number = i) st.passive
  in 
  if Set_of_clauses.is_empty is_in_list then raise (Failure "Not found") else
  (set_active st is_not_in_list; Set_of_clauses.choose is_in_list)


(* the proof protocol *)

type protocol = int * (string * (int * string) list * string) * string

let protocol = ref [(-1,("",[],""),"\n**** Beginning of proof protocol ****")]

let protocol_init () = 
  protocol := [(-1,("",[],""),"\n**** Beginning of proof protocol ****")];
  ()

let protocol_to_string (p:protocol) =
  match p with
    (-1,_,str) -> str
  | (cl_int,info,lits_string) -> 
      ("\n"^(string_of_int cl_int)^": "^lits_string^"  ---  "^(cl_info_to_string info))

let add_to_protocol (p:protocol)  (st:state) = 
  Util.sysout 3 ("\n prot:: "^(protocol_to_string p));
  if st.flags.proof_output > 0 || st.flags.protocol_output then protocol := !protocol @ [p] else ()

let protocol_to_tstp_string (p:protocol) (st:state) =
  let intstringlist_to_string_wo_brackets intstring_list =
    match intstring_list with
       [] -> ""
     | (hdi,hdstr)::tl -> ((List.fold_right (fun (i,str) rs -> (match str with
                                                                      "" -> (rs^","^(string_of_int i)) 
                                                                     | _ -> (rs^","^(string_of_int i)^":"^str)))
                                 tl (match hdstr with
                                       "" -> (string_of_int hdi)
                                     | _ -> ((string_of_int hdi)^":"^hdstr))))
  in
  let intstringlist_to_string intstring_list =
    "["^(intstringlist_to_string_wo_brackets intstring_list)^"]"
  in
  match p with
    (-1,_,str) -> ""
  | (cl_int,(info_string,intstring_list,filename),lits_string) ->  
      let lits_string_for_input str = (String.sub str 1 ((String.length lits_string) - 8)) in    
      match info_string with
	  "axiom" -> ("\n thf("^(string_of_int cl_int)^",axiom,"^(lits_string_for_input lits_string)^","^filename^").")
	| "theorem" -> ("\n thf("^(string_of_int cl_int)^",theorem,"^(lits_string_for_input lits_string)^","^filename^").")
	| "conjecture" -> ("\n thf("^(string_of_int cl_int)^",conjecture,"^(lits_string_for_input lits_string)^","^filename^").")
	| "negated_conjecture" -> ("\n thf("^(string_of_int cl_int)^",negated_conjecture,"^(lits_string_for_input lits_string)^","^filename^").")
	| "negate_conjecture" -> ("\n thf("^(string_of_int cl_int)^",negated_conjecture,("^lits_string^"),inference("^info_string^",[status(cth)],"^(intstringlist_to_string intstring_list)^")).")
	| "split_conjecture" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",["^info_string^"(split,[])],"^(intstringlist_to_string intstring_list)^")).")
	| "solved_all_splits" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",["^info_string^"(join,[])],"^(intstringlist_to_string intstring_list)^")).")
        | "unfold_def" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(thm)],["^(intstringlist_to_string_wo_brackets intstring_list)^st.origproblem_all_def_names^"])).")
	| "extcnf_combined" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(esa)],"^(intstringlist_to_string intstring_list)^")).")
	| "extcnf_forall_neg" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(esa)],"^(intstringlist_to_string intstring_list)^")).")
(*	| "standard_extcnf" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(esa)],"^(intstringlist_to_string intstring_list)^")).")    *)
(*	| "skolemize" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(esa)],"^(intstringlist_to_string intstring_list)^")).") *)
	| "extuni" -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(esa)],"^(intstringlist_to_string intstring_list)^")).")
	| "e" -> ("\n "^lits_string)
	| _ -> ("\n thf("^(string_of_int cl_int)^",plain,("^lits_string^"),inference("^info_string^",[status(thm)],"^(intstringlist_to_string intstring_list)^")).")
	    
let protocollist_to_string (pl:protocol list) =
  List.fold_right (fun s rs -> (protocol_to_string s)^rs) pl ""

let protocollist_to_tstp_string (pl:protocol list) (st:state) =
  (List.fold_right (fun s rs -> (protocol_to_tstp_string s st)^rs) pl "")

let print_protocol () =
  print_string ((protocollist_to_string !protocol)^"\n**** End of proof protocol ****"); 
  print_string ("\n**** no. of clauses: "^(string_of_int (List.length !protocol))^" ****\n")

let print_protocol_tstp (st:state) =
  print_string "\n% SZS output start";
  print_string (protocollist_to_tstp_string !protocol st);
  print_string "\n% SZS output end"; 
  print_string ("\n**** no. of clauses: "^(string_of_int (List.length !protocol))^" ****\n")

let rec find_recursive_entries (intstrl:(int * string) list) (pl:protocol list) =
  let just_parents (p:protocol) = 
    match p with 
      (c_int,(just,parent_ints,filename),str) -> parent_ints
  in
  let just_int (p:protocol) = 
    match p with 
      (c_int,(just,parent_ints,filename),str) -> c_int
  in
  try
    match intstrl with 
      [] -> []
    | (hdi,hdstr)::tl -> 
	let pline = List.find (fun (i,_,_) -> hdi = i) pl in
	(List.fast_sort (fun p1 p2 -> (just_int p1) - (just_int p2))
	   (concat_unique [pline] (find_recursive_entries ((just_parents pline)@tl) pl)))
  with
    Not_found -> []


let derivation (clintstr:(int * string) option) (st:state) =
  let deriv_protocollist =
    match clintstr with
        None -> !protocol
      | Some clintstr' -> find_recursive_entries [clintstr'] (List.rev !protocol) in
  "\n**** Beginning of derivation protocol ****"
  ^(
    match deriv_protocollist with
      [] -> "\n No protocol available -- you may have deactivated the proof output. \n Try command flag-proof-output or option --proofoutput to activate proof output."
    | _::_ ->  (protocollist_to_string deriv_protocollist)
   )
  ^"\n**** End of derivation protocol ****"
  ^"\n**** no. of clauses in derivation: "^(string_of_int (List.length deriv_protocollist))^" ****"
  ^"\n**** clause counter:: "^(string_of_int st.clause_count)^" ****\n"


let derivation_tstp (clintstr:(int * string) option) (st:state) =
  let deriv_protocollist =
    match clintstr with
        None -> !protocol
      | Some clintstr' -> find_recursive_entries [clintstr'] (List.rev !protocol) in
  "\n\n%**** Beginning of derivation protocol ****"
  ^(
    match deriv_protocollist with
      [] -> "\n Clause has not been found in protocol. \n You may have deactivated the proof output. \n Try command flag-proof-output or option --proofoutput to activate proof output."
    | _::_ -> "\n% SZS output start CNFRefutation"
              ^(symbol_types_to_thf st.signature) 
              ^st.origproblem_definitions
              ^(protocollist_to_tstp_string deriv_protocollist st)
              ^"\n% SZS output end CNFRefutation"
   )
  ^"\n\n%**** End of derivation protocol ****"
  ^"\n%**** no. of clauses in derivation: "^(string_of_int (List.length deriv_protocollist))^" ****"
  ^"\n%**** clause counter: "^(string_of_int st.clause_count)^" ****\n"

let print_derivation (clintstr:(int * string) option) (st:state) =
  Util.sysout 0 (derivation clintstr st)

let print_derivation_tstp (clintstr:(int * string) option) (st:state) =
  Util.sysout 0 (derivation_tstp clintstr st)


(* Construction of terms with new symbols *)

let rec create_and_insert_new_free_var_with_simple_name (ty:hol_type) (st:state) =
  let newsym = ("SV"^(string_of_int (inc_free_var_count st))) in
  if is_defined_symbol st.signature newsym || is_uninterpreted_symbol st.signature newsym
  then create_and_insert_new_free_var_with_simple_name ty st (* new try with increased symbol counter *)
  else
    (
     add_uninterpreted_symbol st.signature newsym ty;
     Orderings.symbol_typings := Signature.all_uninterpreted_symbols st.signature; (*FIXME hack -- might be better to store such info in state*)
     Symbol newsym
    )

let rec create_and_insert_new_free_var (t:term) (ty:hol_type) (st:state) =
(* 
   match t with
    Symbol n -> 
      let newsym = ("V_"^n^"_"^(string_of_int (inc_free_var_count st))) in
      if is_defined_symbol st.signature newsym || is_uninterpreted_symbol st.signature newsym
      then create_and_insert_new_free_var t ty st (* new try with increased symbol counter *)
      else
	(
	 add_uninterpreted_symbol st.signature newsym ty;
	 Symbol newsym
	)
  | _ -> raise (Failure "create_and_insert_new_free_var failure")
*)
  create_and_insert_new_free_var_with_simple_name ty st


  
let rec create_and_insert_skolem_const (t:term) (ty:hol_type) (st:state) =
  match t with
    Symbol n -> 
      (* let newsym = ("sK"^(string_of_int (inc_skolem_const_count st))) in *)
      let newsym = ("sK"^(string_of_int (inc_skolem_const_count st))^"_"^n) in 
      let _ =  Util.sysout 3 ("\n New Skolem term: "^newsym^" Type: "^(to_string ty)) in
      if is_defined_symbol st.signature newsym || is_uninterpreted_symbol st.signature newsym
      then create_and_insert_skolem_const t ty st  (* new try with increased symbol counter *)
      else 
	(
	 add_uninterpreted_symbol st.signature newsym ty;
   Orderings.symbol_typings := Signature.all_uninterpreted_symbols st.signature; (*FIXME hack -- might be better to store such info in state*)
	 Symbol newsym
	)
  | _ -> raise (Failure "create_and_insert_skolem_const failure")



let free_var_term (t:term) (st:state) =
  match t with 
    Abstr(x,ty,t) -> 
      let nvar = create_and_insert_new_free_var x ty st in 
      ((beta_normalize (Appl(Abstr(x,ty,t),nvar))),nvar)
  | _ -> raise (Failure "Free var term failure")   
 

(* expand defined logic/non-logic symbols *)

(*
let rec create_new_bound_var_with_simple_name (ty:hol_type) (st:state) =
  let newsym = ("B"^(string_of_int (inc_free_var_count st))) in
  if is_defined_symbol st.signature newsym || is_uninterpreted_symbol st.signature newsym
  then create_new_bound_var_with_simple_name ty st (* new try with increased symbol counter *)
  else
     Symbol newsym



let rename_bound_vars t st =
  Util.sysout 1 ("\n rename_bound_vars term : "^(Term.to_hotptp t));
  let rec help t = 
    match t with
	Appl(t1,t2) -> (Appl(help t1,help t2))
      | Abstr(Symbol varname,ty,t1) -> 
	  let newvar = create_new_bound_var_with_simple_name ty st in
	    (Abstr(newvar,ty,subst_symbols [(varname,newvar)] (help t1)))
      | t -> t
  in
  let res = help t in
    Util.sysout 1 ("\n res rename_bound_vars term : "^(Term.to_hotptp res));
    res
*)

let expand_all_defined_logical_symbols_in_term t (st:state) =
  let defined_symbols = all_defined_symbols st.signature in
  let is_logic_symbol = fun (s,_) -> is_defined_logical_symbol s in
  let defined_logic_symbols =
    List.map
      (fun (s,(t,_)) -> (s,t))
      (List.filter is_logic_symbol defined_symbols)
  in
  subst_symbols defined_logic_symbols t

let rec receive_type_info t pairlist st =
  Util.sysout 4 ("\n   enter receive_type_info : "^(Term.to_hotptp t)^" "^
                   (List.fold_right
                      (fun (v,ty) ll -> ((Term.to_hotptp v)^":"^(to_string ty)^" "^ll)) pairlist ""));
  let result =
    match t with 
        Symbol _ ->         
          begin
            match pairlist with
                [] -> (Term.type_of (type_of_symbol st.signature) t)
              | (v,ty)::rest -> 
                  if t = v (* & (is_polyvar (Term.type_of (type_of_symbol st.signature) v)) *)
                  then ty
                  else receive_type_info t rest st
          end
      | Appl(t1,t2) ->  
          let ty1 =  receive_type_info t1 pairlist st in
          (* let argty1 = arg_type ty1 in *)
          let goalty1 = result_type ty1 in
          (* let ty2 =  receive_type_info t2 pairlist st in
            if argty1 = ty2 || is_polyvar argty1 then *)
              goalty1
          (*
            else 
              raise (Failure ("inconsistent typing: "^(Term.to_hotptp  (Appl(t1,t2)))^"    t1: "^(Term.to_hotptp t1)^"    t2: "^(Term.to_hotptp t2)))
          *)
      | Abstr(v,ty,t1) ->
          let tty = receive_type_info t1 ((v,ty)::pairlist) st in
          let vty = ty in
            Funtype(vty,tty) 
  in
    Util.sysout 4 ("\n   leave receive_type_info : "^(to_string result));
    result

let rec remove_type_info v pairlist =
  match pairlist with
      [] -> []
    | (w,ty)::rest -> 
        if v = w then 
          remove_type_info v rest
        else
          (w,ty)::remove_type_info v rest

let rec combine_pairlists pairlist1 pairlist2 =
  match (pairlist1,pairlist2) with
      ([],l2) -> l2
    | (l1,[]) -> l1
    | ((v1,ty1)::tl1,(v2,ty2)::l2) -> 
        if v1 = v2 then 
          if is_polyvar ty1 then
            combine_pairlists tl1 ((v2,ty2)::l2)
          else 
            if is_polyvar ty2 then
              combine_pairlists tl1 ((v2,ty1)::l2)
            else 
              if ty1 = ty2 then
                combine_pairlists tl1 ((v2,ty2)::l2)
              else 
                raise (Failure "inconsistent typing")
        else 
          (v1,ty1)::(combine_pairlists tl1 ((v2,ty2)::l2))
            
let ground_poly_syms t st =
  let rec help t pairlist st =
    Util.sysout 4 ("\n  enter help : "^(Term.to_hotptp t)^" "^
                     (List.fold_right
                        (fun (v,ty) ll -> ((Term.to_hotptp v)^":"^(to_string ty)^" "^ll)) pairlist ""));
    let (resterm,respairlist) =
      match t with 
          Symbol _ -> (t,pairlist) 
        | Appl(Symbol u,Symbol v) -> 
            let argty1 = arg_type (receive_type_info (Symbol u) pairlist st) in
            let ty2 = (receive_type_info (Symbol v) pairlist st) in
              if is_polyvar ty2 (* & is_polyvar (receive_type_info t pairlist st)) *) then 
                let newpairlist1 = (((Symbol v),argty1)::(remove_type_info (Symbol v) pairlist)) in
                  (Appl(Symbol u,Symbol v),newpairlist1)
              else 
                (Appl(Symbol u,Symbol v),pairlist)
        | Appl(t1,Symbol v) -> 
            let argty1 = receive_type_info t1 pairlist st in
            let ty2 = receive_type_info (Symbol v) pairlist st in
              if (is_polyvar ty2 && is_polyvar (receive_type_info t pairlist st)) then 
                let newpairlist1 = (((Symbol v),argty1)::(remove_type_info (Symbol v) pairlist)) in
                let (t1',newpairlist2) = help t1 newpairlist1 st in
                  (Appl(t1',Symbol v),newpairlist2)
              else 
                let (t1',newpairlist2) = help t1 pairlist st in
                  (Appl(t1',Symbol v),newpairlist2)
        | Appl(t1,t2) -> 
            let (t1',newpairlist1) = (help t1 pairlist st) in
            let (t2',newpairlist2) = (help t2 pairlist st) in
              (Appl(t1',t2'),combine_pairlists newpairlist1 newpairlist2)
        | Abstr(x,ty,t1) ->          
            if is_polyvar ty then
              let (t1',newpairlist1) = (help t1 ((x,ty)::pairlist) st) in
              let newty =  receive_type_info x newpairlist1 st in
              let newpairlist2 = remove_type_info x newpairlist1 in
                ((Abstr(x,newty,t1')),newpairlist2) 
            else 
              let (t1',newpairlist1) = (help t1 ((x,ty)::pairlist) st) in 
                ((Abstr(x,ty,t1')),remove_type_info x newpairlist1)
    in     
      Util.sysout 4 ("\n  leave help : "^(Term.to_hotptp resterm)^" "^
                       (List.fold_right
                          (fun (v,ty) ll -> ((Term.to_hotptp v)^":"^(to_string ty)^" "^ll)) respairlist ""));
      (resterm,respairlist)
  in 
    Util.sysout 4 ("\n enter ground_poly_syms : "^(Term.to_hotptp t));
    let (t',_) = help t [] st in
      Util.sysout 4 ("\n leave ground_poly_syms : "^(Term.to_hotptp t'));      
      t'

let rec unfold_logical_defs t (st:state) =
  Util.sysout 4 ("\n unfold_logical_defs term : "^(Term.to_hotptp t));
  let old_t = t 
  and new_t = expand_all_defined_logical_symbols_in_term t st in
    if old_t = new_t 
    then
      begin
        let res = ground_poly_syms new_t st in
	        Util.sysout 4 ("\n res unfold_logical_defs term : "^(Term.to_hotptp res));
	        res
      end
    else unfold_logical_defs new_t st 

let expand_all_defined_nonlogical_symbols_in_term t (st:state) =
  let defined_symbols = all_defined_symbols st.signature in
  let is_nonlogic_symbol = fun (s,_) -> not (is_defined_logical_symbol s) in
  let defined_logic_symbols =
    List.map
      (fun (s,(t,_)) -> (s,t))
      (List.filter is_nonlogic_symbol defined_symbols)
  in
  subst_symbols defined_logic_symbols t


let rec unfold_nonlogical_defs t (st:state) =
  Util.sysout 3 ("\n unfold_nonlogical_defs term : "^(Term.to_hotptp t));
  let old_t = t 
  and new_t = expand_all_defined_nonlogical_symbols_in_term t st in
    if old_t = new_t 
    then
      (  
	Util.sysout 3 ("\n res unfold_nonlogical_defs term : "^(Term.to_hotptp new_t));
	new_t 
      )
    else unfold_nonlogical_defs new_t st 






(** The Kerber FO translation **)

let rec to_fotptp_cnf = function
    Symbol s -> (
      match s with
	 "$true" -> "$true"
       | "$false" -> "$false"
       | _ -> 
	   if (type_of (term2xterm (Symbol s)) = bt_o) && (is_variable (term2xterm (Symbol s)))
	   then String.lowercase s
	   else s
     )
  | Abstr(_,_,_) -> raise (Failure "to_fotptp_cnf")
  | Appl(Appl(Symbol "=", t1),t2) ->
      if ((type_of (term2xterm t1)) = bt_o) && ((type_of (term2xterm t2)) = bt_o) then 
	("("^(to_fotptp_cnf  t1)^" <=> "^(to_fotptp_cnf  t2)^")")


(* ---------------- *)
(* Chad's bug: *)

      else ("(ty_"^(Hol_type.to_fotptp_cnf (type_of (term2xterm t1)))^"("^(to_fotptp_cnf  t1)^") = "^
            "ty_"^(Hol_type.to_fotptp_cnf (type_of (term2xterm t2)))^"("^(to_fotptp_cnf  t2)^"))")

(* was:      else ("("^(to_fotptp_cnf  t1)^" = "^(to_fotptp_cnf  t2)^")")   *)
(* ---------------- *)


(*
   | Appl(Appl(Symbol binop, t1),t2) -> 
   if symb_is_critical binop then raise (Failure "to_fotptp_cnf")
   else 
   if ((type_of (term2xterm t2)) = bt_o) then raise (Failure "to_fotptp_cnf")
   else ("at("^binop^","^(to_fotptp_cnf  t1)^","^(to_fotptp_cnf  t2)^")")
(*
   then ((to_fotptp_cnf t1)^" "^(hotptpsymb_critical binop)^" "^(to_fotptp_cnf t2)) 
   else (binop^"("^(to_fotptp_cnf t1)^","^(to_fotptp_cnf t2)^")")
 *) 
   | Appl(Symbol unop,t) -> 
   if symb_is_critical unop then raise (Failure "to_fotptp_cnf")
(*
   then ((hotptpsymb_critical unop)^"("^(to_fotptp_cnf t)^")")
 *) 
   else 
   if ((type_of (term2xterm t)) = bt_o) then raise (Failure "to_fotptp_cnf")
   else ("at("^unop^","^(to_fotptp_cnf  t)^")")
 *)
  | Appl(t1,t2) -> 
      if ((type_of (term2xterm t2)) = bt_o) then raise (Failure "to_fotptp_cnf")
      else "at_"^(Hol_type.to_fotptp_cnf (type_of (term2xterm t1)))^"_"^(Hol_type.to_fotptp_cnf (type_of (term2xterm t2)))^"("^(to_fotptp_cnf  t1)^","^(to_fotptp_cnf  t2)^")"
																					      
																					      
let to_fotptp_cnf_xterm = function
    Explicit t -> to_fotptp_cnf  t
  | Indexed(idx,id) -> to_fotptp_cnf (Termset.retrieve idx.termbase id)
	
	
let cl_clause_to_fotptp_cnf_1 (st:state) (clause:cl_clause) = 
    let lit_literal_to_fotptp_cnf (literal:'a lit_literal) =
    if literal.lit_polarity then (to_fotptp_cnf_xterm literal.lit_term)
    else ("(~ "^(to_fotptp_cnf_xterm literal.lit_term)^")")
  in
  let lit_litlist_to_fotptp_cnf (cll:'a lit_literal list) =
    match cll with
       [] -> ""
      | hd::tl ->  (List.fold_left 
		     (fun s i -> ((lit_literal_to_fotptp_cnf i)^" | "^s))  (* ("("^(lit_literal_to_fotptp_cnf i)^" | "^s)^")")  *)
		     (lit_literal_to_fotptp_cnf hd) tl)
  in
  try
    let free_vars = List.map get_symbol clause.cl_free_vars in
    let free_vars_string = 
      match free_vars with
          [] -> ""
	| hd::tl -> "!["^(List.fold_left (fun s str -> s^","^str) hd tl)^"]: " in  
    let litstring = (lit_litlist_to_fotptp_cnf (Array.to_list clause.cl_litarray)) 
    and clause_name = (* ("leo_II_clause_"^(string_of_int clause.cl_number)) *)
          (string_of_int clause.cl_number)
    in [(clause_name,("\n fof("^clause_name^",axiom,"^free_vars_string^"("^litstring^"))."))]
  with Failure "to_fotptp_cnf" -> []
      
      
      
let boolean_constants_and_variables (st:state) =
  List.map (fun (c,t) -> c) (List.filter (fun (c,t) -> t = bt_o) (all_uninterpreted_symbols st.signature))
    
    
let dynamic_tertium_non_datur_axioms_1 (st:state) = 
  []

(*
  let t_true =  "$true" 
  and t_false =  "$false"
  and bool_consts_and_vars = boolean_constants_and_variables st in
(*  print_string ("\n\n ********* tnd-axioms-for "^st.origproblem_filename^" *********\n"); *)
  List.iter (fun c -> print_string c) bool_consts_and_vars;
  List.fold_right
    (fun c l -> 
      let t_c = to_fotptp_cnf (Symbol c)
      and name = ("tnd_"^c) 
      in ((name,("\n fof("^name^",axiom,(("^t_c^" <=> "^t_true^") | ("^t_c^" <=> "^t_false^")))."))::l))
    bool_consts_and_vars []
*)    
    

let cl_clause_to_fotptp_cnf_init_1 = []

(** The fully typed FO translation **)

let rec translate_type_2 = function
    Basetype(n) as ty ->
        if ty = Signature.bt_i then "i"(*FIXME const*)
        else if ty = Signature.bt_o then "o"(*FIXME const*)
        else "t"(*FIXME const*) ^ n
  | Funtype(at,bt) -> ("leoFt("^(translate_type_2 at)^","^(translate_type_2 bt)^")") 


let rec to_str_special = function
    Symbol s -> 
      let new_str =
	match s with
	    "$true"    -> "true"
	  | "$false"   -> "false"
	  | "~"     -> "not"
	  | "|"      -> "or"
	  | "="  ->  "equals"
	  | "!"  ->  "forall"
	  | "^"  ->  "lambda"
	  | s  -> s
      in
	new_str
  | Appl(t1,t2) -> "appl"^(to_str_special t1)^""^(to_str_special t2)
  | Abstr(x,ty,t) -> "abstr"^(to_str_special x)^""^(to_str_special t)

let rec translate_varlist_2_help (sl:string list) =
    match sl with
	[] -> ""
      | [v] -> v
      | hd::tl -> (hd^","^(translate_varlist_2_help tl))


let rec translate_term_2 term argtype = 
  match term with
    Symbol s -> 
      (
       let ty = translate_type_2 (type_of (term2xterm (Symbol s))) in
       match s with
	  "$true"    -> ("leoTi(true,"^ty^")")
	| "$false"   -> ("leoTi(false,"^ty^")")
	| "~"     -> ("leoTi(neg,"^ty^")")
	| "|"      -> ("leoTi(or,"^ty^")")
	| "="  ->  raise (Failure "to_fotptp_cnf")
	| "!"  ->  raise (Failure "to_fotptp_cnf")
	| "^"  ->  raise (Failure "to_fotptp_cnf")
	| s -> ("leoTi("^s^","^ty^")")
      )
  | Abstr(x1,tp,t1) -> 
      (
	let ty = (translate_type_2 (type_of (term2xterm  (Abstr(x1,tp,t1))))) in
	let abs_string = to_str_special (Abstr(x1,tp,t1)) in
	let free_vars = Term.free_vars (Abstr(x1,tp,t1)) in
	let res =
	  if free_vars = [] 
	  then "leoTi("^abs_string^","^ty^")" 
	  else
	    let varlist_str = translate_varlist_2_help free_vars in
	      "leoTi("^abs_string^"("^varlist_str^")"^","^ty^")" 
	in
	  Util.sysout 3 ("\n Abstr: "^(Term.to_string  (Abstr(x1,tp,t1))));
	  Util.sysout 3 ("\n Trans: "^res);
	  res
       )
  | Appl(t1,t2) -> 
      let ty = translate_type_2 (type_of (term2xterm (Appl(t1,t2)))) in
      let argtype = (type_of (term2xterm t2)) in 
        ("leoTi(leoAt("^(translate_term_2 t1 argtype)^","^(translate_term_2 t2 argtype)^"),"^ty^")") 

let cl_clause_to_fotptp_cnf_2 (st:state) (clause:cl_clause) =
  let translate_top_term_2 = function
      Appl(Appl(Symbol "=", t1),t2) -> let dummytp = (Basetype "$i") in (true,((translate_term_2 t1 dummytp)^" = "^(translate_term_2 t2 dummytp)))
    | Appl(Appl(Symbol "!=", t1),t2) -> let dummytp = (Basetype "$i") in (true,((translate_term_2 t1 dummytp)^" != "^(translate_term_2 t2 dummytp)))
    | t -> let dummytp = (Basetype "$i") in (false,translate_term_2 t dummytp) in
  let translate_lit_2 (literal:'a lit_literal) =
    let (eq_flag,transterm) = (translate_top_term_2 (xterm2term literal.lit_term)) in
    if eq_flag 
    then (if literal.lit_polarity then transterm else ("(~ "^transterm^")"))
    else (if literal.lit_polarity then ("leoLit("^transterm^")") else ("(~ leoLit("^transterm^"))")) in
  let translate_litlist_2 (cll:'a lit_literal list) =
    match cll with
       [] -> ""
     | hd::tl ->  (List.fold_left 
		     (fun s i -> ("("^(translate_lit_2 i)^" | "^s)^")") 
		     (translate_lit_2 hd) tl) in
  try
    let free_vars = List.map get_symbol clause.cl_free_vars in
    let free_vars_string = 
      match free_vars with
          [] -> ""
	| hd::tl -> "!["^(List.fold_left (fun s str -> s^","^str) hd tl)^"]: " in  
    let litstring = (translate_litlist_2 (Array.to_list clause.cl_litarray)) 
    and clause_name = (* ("leo_II_clause_"^(string_of_int clause.cl_number)) *)
         (string_of_int clause.cl_number)
    in [(clause_name,("\n fof("^clause_name^",axiom,"^free_vars_string^"("^litstring^"))."))]
  with Failure "to_fotptp_cnf" -> (Util.sysout 3 ("\n No FOF translation for clause "^(cl_clause_to_string clause)); [])



(** New stuff May 2012 to provide some initial translation to FOF for quick attacks with FOF ATP **)

let rename_free_variable (t:role xterm) (var:role xterm) (ty:hol_type) (st:state) =
  let _ = Util.sysout 5 ("\nEnter rename_free_variable with \n t: "^(Termsystem.to_string t)^" var: "^(Termsystem.to_string var)^" ty: "^(to_string ty)) in
  let new_var = term2xterm (create_and_insert_new_free_var_with_simple_name ty st) in
  let _ = Util.sysout 5  ("\n Inside1 rename_free_variable with \n new_var: "^(Termsystem.to_string new_var)) in
  let subst_term = substitute st.index t [(var,new_var)] in
  let _ = Util.sysout 5  ("\n Inside2 rename_free_variable with \n subst_term: "^(Termsystem.to_string subst_term)) in
  let result =  (xterm2term subst_term,new_var) in
  let _ = Util.sysout 5 ("\nLeaving rename_free_variable\n") in
  result


let cl_clause_to_fof_simple (clause:cl_clause) (st:state) =
  let is_special_symbol s = 
    let res = List.exists (fun sym -> (sym = s)) interpreted_constants
    in  
      Util.sysout 5 ("\n  is special "^s^" : "^(string_of_bool res));
      res
  in
  let rec appl_to_fof_simple  (term:term) = 
    Util.sysout 5 ("\n appl_to_fof_simple: "^(Term.to_string term));
    let rec help (t:term) =
    Util.sysout 5 ("\n  help: "^(Term.to_string t));
      match t with 
	| Appl(Symbol s,t1) -> 
          if is_special_symbol s
          then raise (Failure "fof translation error")
          else (s^"("^(appl_to_fof_simple t1))
	| Appl(t1,t2) -> ((help t1)^","^(appl_to_fof_simple t2))
	| Symbol s -> 
          if is_special_symbol s
          then raise (Failure "fof translation error")
          else (s^"(")
	| _ -> raise (Failure "fof translation error")
    in
    let res =
      match term with
	| Appl(Symbol s,t1) -> 
          if is_special_symbol s
          then raise (Failure "fof translation error")
          else (s^"("^(appl_to_fof_simple t1)^")")
	| Appl(t1,t2) -> ((help t1)^","^(appl_to_fof_simple t2)^")")
	| Symbol s -> if is_special_symbol s
          then raise (Failure "fof translation error")
          else s
	| _ -> raise (Failure "fof translation error")
    in
      Util.sysout 5 ("\n res: "^res);
      res
  in
  let rec term_to_fof_simple  (term:term) = 
    Util.sysout 5 ("\nterm_to_fof_simple: "^(Term.to_string term));
    match term with 
      | Symbol s -> s
      | Appl(Symbol "~",t1) -> ("(~ "^(term_to_fof_simple t1)^")")
      | Appl(Appl(Symbol "|",t1),t2) -> ("("^(term_to_fof_simple t1)^" | "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "~|",t1),t2) -> ("("^(term_to_fof_simple t1)^" ~| "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "&",t1),t2) -> ("("^(term_to_fof_simple t1)^" & "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "~&",t1),t2) -> ("("^(term_to_fof_simple t1)^" ~& "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "=>",t1),t2) -> ("("^(term_to_fof_simple t1)^" => "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "<=",t1),t2) -> ("("^(term_to_fof_simple t1)^" <= "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "<=>",t1),t2) -> ("("^(term_to_fof_simple t1)^" <=> "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "<~>",t1),t2) -> ("("^(term_to_fof_simple t1)^" <~> "^(term_to_fof_simple t2)^")")
      | Appl(Appl(Symbol "=" as c,t1),t2)
      | Appl(Appl(Symbol "!=" as c,t1),t2) ->
          let ty = type_of (term2xterm t1) in
            if ty = Signature.bt_i then
              "(" ^ appl_to_fof_simple t1 ^ " " ^ Term.get_symbol c ^ " " ^
                appl_to_fof_simple t2 ^")"
            else raise (Failure "fof translation error")
      | Appl(Symbol "!" as q, Abstr (Symbol x, ty, t1))
      | Appl(Symbol "?" as q, Abstr (Symbol x, ty, t1)) ->
          if ty = Signature.bt_i then
            let (new_term,new_var) = rename_free_variable (term2xterm t1) (term2xterm (Symbol x)) Signature.bt_i st in
              ("(" ^ Term.get_symbol q ^ "["^(Termsystem.to_string new_var)^"]: "^(term_to_fof_simple new_term)^")")
          else raise (Failure "fof translation error")
      | Appl(t1,t2) -> (appl_to_fof_simple (Appl(t1,t2)))
      | _ -> raise (Failure "fof translation error")
  in
  let unitclause_to_fof_simple (clause:cl_clause) =
    match (Array.to_list clause.cl_litarray) with 
	[lit] ->
	  (
	    let form = (xterm2term lit.lit_term) in
	    let res_pre = 
	      try term_to_fof_simple form
	      with Failure _ -> ""
	    in
	      if res_pre = "" then []
	      else
                let res = match lit.lit_polarity with true -> res_pre | false -> "(~ "^res_pre^")"  
	        in
		let clause_name = (string_of_int clause.cl_number) in
		  match clause.cl_origin with
		      AXIOM -> 
			[(clause_name,("\n fof("^clause_name^",axiom,"^res^")."))]
		    | CONJECTURE -> 
			[(clause_name,("\n fof("^clause_name^",negated_conjecture,"^res^")."))]
		    | DERIVED -> 
			[(clause_name,("\n fof("^clause_name^",axiom,"^res^")."))]
	  )
      | _ -> []
  in
  let res = 
    try unitclause_to_fof_simple clause 
    with Failure _ -> [] 
  in
  let str = match res with 
      [] -> ""
    | [(_,trans)] -> trans
    | _ -> ""
  in
    Util.sysout 5 ("\nclause "^(cl_clause_to_protocol clause)^" translated to"^str^"\n");
    res
	  
 
	  



	  
 
(*** end new stuff May 2012 ***)

(*
let cl_clause_to_fotptp_cnf_init_2 =   (* Encoding of BOolean Algebra *)
  let ty_o = (translate_type_2 bt_o) 
  and ty_oo = (translate_type_2 (Funtype(bt_o,bt_o))) in
  let t_x = ("ti(X,"^ty_o^")")
  and t_y = ("ti(Y,"^ty_o^")")
(*  and t_z = ("ti(Z,"^ty_o^")") *)
  and t_true =  translate_term_2 (Symbol "$true")
  and t_false = translate_term_2 (Symbol "$false")
  and t_neg = translate_term_2 (Symbol "~")
  and t_or = translate_term_2 (Symbol "|") in
  let appl_1 t1 t2 = ("ti(at("^t1^","^t2^"),"^ty_o^")") in 
  let appl_2 t1 t2 t3 = 
    let t_new = ("ti(at("^t1^","^t2^"),"^ty_oo^")") in
    appl_1 t_new t3 in
  let boolean_agebra_axioms =
    let triples =
	[
	 ("ba_axiom_commutativity_or",(appl_2 t_or t_x t_y),(appl_2 t_or t_y t_x));
(*	 ("ba_axiom_assiociativity_or",(appl_2 t_or (appl_2 t_or t_x t_y) t_z),(appl_2 t_or t_x (appl_2 t_or t_y t_z))); *)(* when associativity is added the FO provers die in the search space *)
	 ("ba_axiom_complement_or",(appl_2 t_or t_x (appl_1 t_neg t_x)),t_true);
	 ("ba_axiom_idempotency_or",(appl_2 t_or t_x t_x),t_x);
	 ("ba_axiom_boundedness_1_or",(appl_2 t_or t_x t_true),t_true);     
	 ("ba_axiom_boundedness_2_or",(appl_2 t_or t_x t_false),t_x);  
	 ("ba_axiom_complements_1_neg",(appl_1 t_neg t_false),t_true);
	 ("ba_axiom_complements_2_neg",(appl_1 t_neg t_true),t_false);
	 ("ba_axiom_complements_2_neg",(appl_1 t_neg (appl_1 t_neg t_x)),t_x)
       ] in
    List.fold_right
      (fun (n,l,r) ll -> ((n,("\n fof("^n^",axiom,("^l^" = "^r^"))."))::ll))
      triples []
  in
  let lit_boolean_agebra_connection_axioms =
    let triples =
      [
       ("lit_ba_connection_1",("lit("^t_true^")"),"$true");
       ("lit_ba_connection_2",("lit("^t_false^")"),"$false")
     ] in
    List.fold_right
      (fun (n,l,r) ll -> ((n,("\n fof("^n^",axiom,("^l^" <=> "^r^"))."))::ll))
      triples []
  in
  (lit_boolean_agebra_connection_axioms@boolean_agebra_axioms)
*)

let cl_clause_to_fotptp_cnf_init_2 = []

let cl_clause_to_fof_simple_init = []  

(*
let boolean_constants (st:state) =
  List.map (fun (c,t) -> c) (List.filter (fun (c,t) -> t = bt_o) (all_uninterpreted_symbols st.signature))
*)


(* removed 25.09.2009 because of SUMO time refinement examples 

let dynamic_tertium_non_datur_axioms_2 (st:state) =    
  let t_true =  translate_term_2 (Symbol "$true") 
  and t_false =  translate_term_2 (Symbol "$false") 
  and bool_consts_and_vars = boolean_constants_and_variables st in
(*  print_string ("\n\n ********* tnd-axioms-for "^st.origproblem_filename^" *********\n"); *)
  (* List.iter (fun c -> print_string c) bool_consts_and_vars; *)
  List.fold_right
    (fun c l -> 
      let t_c = (translate_term_2 (Symbol c))
      and name = ("tnd_"^c) 
      in ((name,("\n fof("^name^",axiom,(("^t_c^" = "^t_true^") | ("^t_c^" = "^t_false^")))."))::l))
    bool_consts_and_vars []

*)
  
let dynamic_tertium_non_datur_axioms_2 (st:state) =  []  




(*
  let var_x = create_and_insert_new_free_var_with_simple_name bt_o st
  and var_y = create_and_insert_new_free_var_with_simple_name bt_o st in
  add_to_index st var_x;
  add_to_index st var_y;
  let pairs =
    [((Appl(Appl(Symbol disjunction,var_x),var_y)),
      (Appl(Appl(Symbol disjunction,var_x),var_y)));
     ((Appl(Appl(Symbol disjunction,var_x),var_y)),
      (var_x))
   ] in 
  List.iter (fun (l,r) -> (add_to_index st l); (add_to_index st r)) pairs;
  List.fold_right
    (fun (l,r) s -> (s^"\n fof(boolean_algebra,axiom,("^(translate_term_2 l)^" = "^(translate_term_2 r)^")).")) pairs ""
  *)  
      
    



(* building and maintaining the fo_tptp clauses *)

let cl_clause_to_fotptp_cnf (clause:cl_clause) (st:state) =
  match st.flags.fo_translation with
    "kerber" -> cl_clause_to_fotptp_cnf_1 st clause
  | "fully-typed" -> cl_clause_to_fotptp_cnf_2 st clause
  | "simple" ->  cl_clause_to_fof_simple clause st
  | _ -> failwith "No FO translation specified"

(*FIXME This function doesn't appear to do anything*)
let cl_clause_to_fotptp_cnf_init (st:state) =
  match st.flags.fo_translation with
    "kerber" -> cl_clause_to_fotptp_cnf_init_1
  | "fully-typed" -> cl_clause_to_fotptp_cnf_init_2 
  | "simple" ->  cl_clause_to_fof_simple_init 
  | _ ->
      (*In this case we're probably using one of the translations
        in the Translation module*)
      []

(*Simply transfers some given of FO clauses into the state without applying
  any processing (cf. add_fo_clauses) but while ensuring that no
  duplicately-named clauses are added*)
let add_fo_clauses_direct (st : state) =
  List.iter
    (fun (n, fo_cl) ->
       try
         ignore(List.assoc n st.fo_clauses)
       with
           Not_found ->
             st.fo_clauses <- (n, fo_cl) :: st.fo_clauses)

let fo_clauses_init (st : state) =
  add_fo_clauses_direct st (cl_clause_to_fotptp_cnf_init st)

let add_fo_clauses (cll:cl_clause list) (st:state) =
  add_fo_clauses_direct st (List.flatten (List.map (fun c -> cl_clause_to_fotptp_cnf c st) cll))

let get_fo_clauses (st:state) = 
  List.iter
    (fun (n, fo_cl) ->
       try ignore(List.assoc n st.fo_clauses) with
           Not_found ->
             st.fo_clauses <- (n, fo_cl) :: st.fo_clauses)
    (match st.flags.fo_translation with
         "kerber" -> dynamic_tertium_non_datur_axioms_1 st
       | "fully-typed" -> dynamic_tertium_non_datur_axioms_2 st
       | "simple" -> []
       | _ ->
           (*In this case we're probably using one of the
             translations in the Translation module*)
           []);
  (*Imp. to reverse the fo_cl in the string*)
  List.fold_right (fun (_, fo_cl) s -> s ^ fo_cl) st.fo_clauses ""

let get_fo_clauses_numbers (st:state) = 
  List.fold_right (fun (n, _) l -> int_of_string n :: l) st.fo_clauses []

let check_local_max_time (st:state) =
  let seconds_left = st.flags.max_local_time - (int_of_float (Sys.time ()))  in 
    Util.sysout 1 ("<SecLeft="^(string_of_int seconds_left)^">");
    if seconds_left < 0 
    then 
      let _ = Util.sysout 1 (" Running out of time, I should stop! ") in
	true
    else
      false



(*Builds a clause value. This is a frequently-called function*)
let rec mk_clause (litlist : role lit_literal list) (cl_number : int)
 (free_vars : term list) (info : cl_info) (origin : cl_origin) (st : state) : Clause.cl_clause =
  (*Add !-quantifier prefix to the list of literals*)
  let quantified_litlist_string (ll : role lit_literal list) : string =
    let typed_free_vars_list =
      List.map
        (fun v -> Term.to_hotptp v ^ ":" ^
           Hol_type.to_hotptp (Term.type_of (type_of_symbol st.signature) v))
        free_vars
    in match typed_free_vars_list with (*FIXME style*)
        [] -> lit_litlist_to_protocol ll
      | hd :: tl -> "![" ^
          List.fold_left (fun s str -> s ^ "," ^ str) hd tl ^
            "]: (" ^ lit_litlist_to_protocol ll ^ ")"
  in
    if litlist = [] then
      let newlitlist = [lit_mk_pos_literal st.signature (Explicit (Symbol cfalse))] in
      let newclause = cl_mk_clause newlitlist cl_number free_vars info origin in
        add_to_protocol (cl_number, info, quantified_litlist_string newlitlist) st;
        add_to_protocol (cl_number + 1, ("dummyTSTP", [(cl_number, "")], ""), "$false") st;
        ignore(set_empty_clauses st (newclause :: st.empty_clauses));
        begin
          match global_conf.operating_mode with
              Theorem_vs_CounterSatisfiable -> set_current_success_status (Some st) Theorem
            | Unsatisfiable_vs_Satisfiable -> set_current_success_status (Some st) Unsatisfiable
        end;
        raise EMPTYCLAUSE_DERIVED
    else
      let newclause = cl_mk_clause litlist cl_number free_vars info origin in
        add_to_protocol (cl_number, info, quantified_litlist_string litlist) st;
        Util.sysout 2 (string_of_int st.clause_count ^ " ");
        if List.for_all (fun l -> is_flexflex_unilit l) litlist then
          mk_clause [] (inc_clause_count st) []
            ("flexflex", [(newclause.cl_number, "")], "") origin st
        else
          if st.flags.max_clause_count > 0  &&
            st.clause_count >= st.flags.max_clause_count then
              begin
                set_current_success_status (Some st) GaveUp;
                raise MAX_CLAUSES
              end
          else 
	      newclause

(* index with role *)

let index_clause_with_role (cl:cl_clause) (st:state) =
  let lit_index_with_role (lit:role lit_literal) (role:role) (st:state) = index_with_role st.index lit.lit_term role in
  for i=0 to (Array.length cl.cl_litarray) - 1 do
    let lit = (Array.get cl.cl_litarray i) in
    let max_info = if i < cl.cl_max_lit_num then "max" else "nmax" and
	pol_info = if lit.lit_polarity then "pos" else "neg" in
    let _ = lit_index_with_role lit (cl.cl_number,i,max_info,pol_info) st in
    ()
  done

let index_clauselist_with_role (cll:cl_clause list) (st:state) =
  List.iter (fun cl -> index_clause_with_role cl st) cll


let index_clear_all_roles (st:state) = clear_role_index st.index

(* mk_clause and index with roles *)

let mk_clause_and_index_with_role (litlist:role lit_literal list) (int:int) (free_vars:term list) (info:cl_info) (origin:cl_origin) (st:state) = 
  let newclause =  mk_clause litlist int free_vars info origin st in
  index_clause_with_role newclause st;
  newclause

let choose_and_remove_lightest_from_active (st : state) =
  if Set_of_clauses.is_empty st.active then
    begin
      set_current_success_status (Some st) GaveUp;
      raise ACTIVE_EMPTY
    end
  else
    let lightest = Set_of_clauses.min_elt st.active
    in
      begin
        IFDEF DEBUG THEN Util.sysout 2 ("\n Lightest Clause : " ^ cl_clause_to_string lightest) END;
        (* destructive removal of lightest from active *)
        let length1 = List.length (Set_of_clauses.elements st.active) in 
        let _ = set_active st (Set_of_clauses.remove lightest st.active) in 
        let length2 = List.length (Set_of_clauses.elements st.active) in 
          if (length2 >= length1) then
            begin
              Util.sysout 0 ("\n CLAUSE-REMOVAL-PROBLEM: "^(cl_clause_to_string lightest));
              Util.sysout 0 ("\n lightest \\in Active: " ^ string_of_bool (Set_of_clauses.mem lightest st.active));
              Util.sysout 0 ("\n compare lightest lightest: " ^ string_of_int (Clauseset.ratio_strategy lightest lightest))
            end;
          lightest
      end

let origproblem_to_string (st:state) =
  (* Hashtbl.fold (fun s tp init -> let (n,t)=tp in "\n  "^s^" "^n^": "^(Term.to_hotptp t)^" "^init) st.origproblem *) 
  "origproblem not displayed"



(*
let problem_stack_to_string prob_stack =
  let rec help prob_stack =
    match prob_stack with
	[] -> ""
      | (conjecture_list,axiom_list)::rl -> 
	  "\n"^(cl_clauselist_to_string conjecture_list)^"\nwith\n"^(cl_clauselist_to_string axiom_list)^"\n"^(help rl)
  in
    "<<"^(help prob_stack)^">>"
*)

let state_to_string (st:state) =
  (
   "\n"
   ^"ORIGPROBLEM: "^(origproblem_to_string st)^"\n"
   ^"ORIGPROBLEM_FILENAME: "^st.origproblem_filename^"\n"
   ^"ORIGPROBLEM_DEFINITIONS: "^st.origproblem_definitions^"\n"	
   ^"ORIGPROBLEM_ALL_DEF_NAMES: "^st.origproblem_all_def_names^"\n"	
   ^"SIGNATURE: "^(signature_to_string st.signature)
^"\n"
   ^"INDEX: Index not displayed here since it usually becomes to big (use command analyze-index)\n" 
   ^"ACTIVE: "^(cl_clauseset_to_string st.active)^"\n"
   ^"PASSIVE: "^(cl_clauseset_to_string st.passive)^"\n"
   ^"PRIMSUBST_WAITLIST: "^(cl_clauseset_to_string st.primsubst_waitlist)^"\n"
   ^"PROBLEM_AXIOMS: "^(cl_clauselist_to_string st.problem_axioms)^"\n"
   ^"PROBLEM_STACK: "^(cl_clauselist_to_string st.problem_stack)^"\n"
   ^"FREE_VAR_COUNT: "^(string_of_int st.free_var_count)^" " 
   ^"SKOLEM_CONST_COUNT: "^(string_of_int st.skolem_const_count)^" "
   ^"CLAUSE-COUNT: "^(string_of_int st.clause_count)^"\n"
   ^"LOOP-COUNT: "^(string_of_int st.loop_count)^"\n" 
   ^"CLAUSE_WEIGHT_FUNC: Not displayed here\n"
   ^"EMPTY_CLAUSES: "^(cl_clauselist_to_string st.empty_clauses)^"\n"
   ^"FO_CLAUSES: Not displayed here\n"
   ^"FLAGS: "^"VERBOSE="^(string_of_bool st.flags.verbose)^" MAX_CLAUSE_COUNT="^(string_of_int st.flags.max_clause_count)^" MAX_LOOP_COUNT="^(string_of_int st.flags.max_loop_count)^" MAX_UNI_DEPTH="^(string_of_int st.flags.max_uni_depth)^" WRITE_PROTOCOL_FILES="^(string_of_bool st.flags.write_protocol_files)^" WRITE_FO_LIKE_CLAUSES="^(string_of_bool st.flags.write_fo_like_clauses)^" PRETTY_PRINT_ONLY="^(string_of_bool st.flags.pretty_print_only)^" FO_TRANSLATION="^st.flags.fo_translation^" ATP_CALLS_FREQUENCY="^(string_of_int st.flags.atp_calls_frequency)^" ATP_PROVER="^st.flags.atp_prover^" ATP_TIMEOUT="^(string_of_int st.flags.atp_timeout)^" PROOF_OUTPUT="^(string_of_int st.flags.proof_output)^" PRIM_SUBST="^(string_of_int st.flags.prim_subst)^" REPLACE_LEIBNIZEQ="^(string_of_bool st.flags.replace_leibnizEQ)^" REPLACE_ANDREWSEQ="^(string_of_bool st.flags.replace_andrewsEQ)^" USE_CHOICE="^(string_of_bool st.flags.use_choice)^" UNFOLD_DEFS_EARLY="^(string_of_bool st.flags.unfold_defs_early)^" RELEVANCEFILTER="^(string_of_int st.flags.relevance_filter)^" MAXLOCALTIME="^(string_of_int st.flags.max_local_time)^" SOS="^(string_of_bool st.flags.sos)
   ^"\n"
  )


(** kann weg	    
let clauseconjunction (cll:cl_clause list) =
  let litlist_to_post (cll:lit_literal list) =
    match cll with
      [] -> ""
    | hd::tl ->  (List.fold_left 
		    (fun s i -> ("(or "^(lit_literal_to_post i)^" "^s^")")) 
		    (lit_literal_to_post hd) tl)
  in
  let cl_clause_to_post (clause:cl_clause) = (litlist_to_post (Array.to_list clause.cl_litarray))
  in
  match cll with
    [] -> ""
  | hd::tl -> (List.fold_left 
		 (fun s i -> ("(and "^(cl_clause_to_post i)^" "^s^")")) 
		 (cl_clause_to_post hd) tl)    
*)


let cl_clause_to_post (clause:cl_clause) = (lit_litlist_to_post (Array.to_list clause.cl_litarray))

let clauseconjunction (cll:Set_of_clauses.t) =
  if Set_of_clauses.is_empty cll then ""
  else (Set_of_clauses.fold 
	  (fun i s -> ("(and "^(cl_clause_to_post i)^" "^s^")")) 
	  (Set_of_clauses.remove (Set_of_clauses.min_elt cll) cll)
	  (cl_clause_to_post (Set_of_clauses.min_elt cll)))    

	
let type_variables_to_post (st:state) =
  let tvars = (List.sort String.compare (all_type_vars st.signature))
  in 
  List.fold_left (fun s v -> s^" "^v) "" tvars

let variables_to_post (st:state) =
  let (vars,_) = 
    List.partition 
      (fun (s,i) -> (String.get s 0) >= 'A' && (String.get s 0) <= 'Z') 
(*      (fun (s,i) -> (Char.uppercase (String.get s 0) = String.get s 0)) *)
      (List.sort Hol_type.compare_string_type_pair (all_uninterpreted_symbols st.signature))
  in 
  List.fold_left (fun s (t,i) -> s^" ("^t^" "^(Hol_type.to_post i)^")") "" vars
    
let constants_to_post (st:state) =
  let (_,consts) = 
    List.partition (fun (s,i) -> (String.get s 0) >= 'A' && (String.get s 0) <= 'Z') 
(*    List.partition (fun (s,i) -> (Char.uppercase (String.get s 0) = String.get s 0)) *) 
      (List.sort Hol_type.compare_string_type_pair (all_uninterpreted_symbols st.signature))
  in 
  List.fold_left (fun s (t,i) -> s^" ("^t^" "^(Hol_type.to_post i)^")") "" consts


let constants_to_hotptp (st:state) =
  let rec removeduplicates l rl = 
    match l with
	[] -> rl
      | hd::tl -> removeduplicates tl (if List.mem hd rl then rl else hd::rl)
  in
  let (_,consts) = 
    List.partition (fun (s,i) -> (String.get s 0) >= 'A' && (String.get s 0) <= 'Z') 
(*    List.partition (fun (s,i) -> (Char.uppercase (String.get s 0) = String.get s 0))  *)
      (List.sort Hol_type.compare_string_type_pair (all_uninterpreted_symbols st.signature))
  in
  let (_,defs) = 
    List.partition (fun (s,i) -> (String.get s 0) >= 'A' && (String.get s 0) <= 'Z') 
      (*    List.partition (fun (s,i) -> (Char.uppercase (String.get s 0) = String.get s 0)) *)
      (List.sort Signature.compare_defns (all_defined_symbols_without_logical_symbols st.signature))
  in
  let pre_result =
    ((List.map (fun (t,i) -> "thf("^t^"_type,type,(\n    "^t^": "^(Hol_type.to_hotptp i)^" )).\n\n") consts)
    @(List.map (fun (t,_) -> "thf("^t^"_type,type,(\n    "^t^": "^(Hol_type.to_hotptp (type_of_symbol st.signature t))^" )).\n\n") defs))
  in
  let result = List.fold_left (fun s l -> s^l) "" (removeduplicates pre_result [])
  in
    result
      

let definitions_to_hotptp (st:state) =
  let (_,defs) = 
    List.partition (fun (s,i) -> (String.get s 0) >= 'A' && (String.get s 0) <= 'Z') 
(*    List.partition (fun (s,i) -> (Char.uppercase (String.get s 0) = String.get s 0)) *)
      (all_defined_symbols_without_logical_symbols st.signature)
  in 
  List.fold_left (fun s (t,(term,_)) -> s^"thf("^t^",definition,(\n    "^t^" := ("^(Term.to_hotptp term)^" ) )).\n\n") "" defs



let state_to_post (st:state) =
  "\n(th~defproblem state \n" 
  ^ "  (in base)\n"
  ^ "  (type-variables "^(type_variables_to_post st)^")\n"
  ^ "  (variables "^(variables_to_post st)^")\n"
  ^ "  (constants "^(constants_to_post st)^")\n"
  ^ (List.fold_left (fun s cl -> "  (axiom "^(string_of_int cl.cl_number)^"\n    "^(cl_clause_to_post cl)^")\n"^s) "" (Set_of_clauses.elements st.active))
  ^ (List.fold_left (fun s cl -> "  (axiom "^(string_of_int cl.cl_number)^"\n    "^(cl_clause_to_post cl)^")\n"^s) "" (Set_of_clauses.elements st.passive))
  ^ "(conclusion conc false))\n"
							
							
let origproblem_to_post (st:state) =
  let theorems = (Hashtbl.find_all st.origproblem "theorem") and
      conjectures = (Hashtbl.find_all st.origproblem "conjecture") and 
      axioms = (Hashtbl.find_all st.origproblem "axiom") in
  let _ = 
    match (theorems,conjectures) with
       ([_],[]) -> "theorem"
     | ([],[_]) -> "conjecture"
     | _ -> raise (Failure "Exactly one theorem or conjecture is expected.\n")
  in
  List.fold_left 
    (fun s (str,thm) -> 
      ("\n(th~defproblem "^str^"-origproblem \n"
       ^ "  (in base)\n"
       ^ "  (type-variables "^(type_variables_to_post st)^")\n"
       ^ "  (variables "^(variables_to_post st)^")\n"
       ^ "  (constants "^(constants_to_post st)^")\n"
       ^ "  (definitions "^(st.origproblem_definitions)^")\n"
       ^ (List.fold_left (fun s (str,trm) -> "  (axiom "^str^"\n    "^(Term.to_post trm)^")\n"^s) "" axioms)
       ^ "  (conclusion "^str^"\n"
       ^ "    ("^(Term.to_post thm)^")))\n\n")^s)
    "" (List.append theorems conjectures)




let origproblem_to_hotptp (st:state) =
  let theorems = (Hashtbl.find_all st.origproblem "theorem") and
      conjectures = (Hashtbl.find_all st.origproblem "conjecture") and 
      axioms = (Hashtbl.find_all st.origproblem "axiom") in
  let tp = 
    match (theorems,conjectures) with
       ([_],[]) -> "theorem"
     | ([],[_]) -> "conjecture"
     | _ -> raise (Failure "Exactly one theorem or conjecture is expected.\n")
  in
  List.fold_left 
    (fun s (str,thm) -> 
      ( 
	(* "\n%----Signature \n" *)
	(constants_to_hotptp st) 
	(* ^"%----Definitions" *)
        ^(st.origproblem_definitions)
	(* ^"\n\n%----Axioms \n"*)
	^(List.fold_left (fun s (str,trm) -> "thf("^str^",axiom,(\n    ( "^(Term.to_hotptp trm)^" ) )).\n\n"^s) "" axioms)
	(* ^"\n%----Conjecture \n" *)
	^ "thf("^str^","^tp^",(\n"
	^ "    ( "^(Term.to_hotptp thm)^" ) )).\n\n")^s
    )
    "" (List.append theorems conjectures)



let output (st:state) (f: unit -> string) = 
  if st.flags.verbose  
  then print_string (f ())
  else ()

let output_debug (s:string) = 
  if true  (* change here *)
  then print_string s
  else ()



let uninterpreted_and_nonlogical_symbols_in_clause (cl:cl_clause) (st:state) =
  let rec umerge l1 l2 =
    match l2 with
        a::res -> (if List.mem a l1
                   then umerge l1 res
                   else umerge (a::l1) res)
      | [] -> l1
  in
  let rec get_symbols t =
    if Termsystem.is_symbol t
    then
      let s=Termsystem.dest_symbol t in
      if Signature.is_fixed_logical_symbol st.signature s
      then []
      else [t]
    else if Termsystem.is_appl t
    then
      let (f,a) = Termsystem.dest_appl t in
      umerge (get_symbols f) (get_symbols a)
    else if Termsystem.is_abstr t
    then
      let (_,_,b) = Termsystem.dest_abstr t in
      get_symbols b
    else []
  in
  let termlist = List.map Literal.lit_term (Array.to_list (Clause.cl_litarray cl)) in
  List.fold_left umerge [] (List.map get_symbols termlist) 
  


(** expand definitions in clause **)

let expand_nonlogical_defs (cl:cl_clause) (st:state) =
  let lits = Array.to_list cl.cl_litarray in
  let newlits = 
    List.map 
      (fun l -> 
	 if l.lit_polarity then
     lit_mk_pos_literal st.signature (term2xterm (unfold_nonlogical_defs (xterm2term l.lit_term) st))
	 else
     lit_mk_neg_literal st.signature (term2xterm (unfold_nonlogical_defs (xterm2term l.lit_term) st))
      )
      lits 
  in 
    [mk_clause newlits (inc_clause_count st) 
       (cl.cl_free_vars) ("unfold_def",[(cl.cl_number,"")],"") cl.cl_origin st]

let expand_logical_defs (cl:cl_clause) (st:state) =
  let lits = Array.to_list cl.cl_litarray in
  let newlits = 
    List.map 
      (fun l -> 
	 if l.lit_polarity then
     lit_mk_pos_literal st.signature (term2xterm (unfold_logical_defs (xterm2term l.lit_term) st))
	 else
     lit_mk_neg_literal st.signature (term2xterm (unfold_logical_defs (xterm2term l.lit_term) st)))
      lits 
  in 
    [mk_clause newlits (inc_clause_count st) 
       (cl.cl_free_vars) ("unfold_def",[(cl.cl_number,"")],"") cl.cl_origin st]
      
