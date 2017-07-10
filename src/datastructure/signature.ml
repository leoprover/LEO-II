(* ========================================================================= *)
(* The Signature                                                             *)
(* ========================================================================= *)

open Hol_type
open Term
open List

type ('a,'b) hashtbl = ('a,'b) Hashtbl.t

type signature = {
  mutable basetypes : hol_type list;
  mutable typevars  : string list;
          fixedlogs : (string, hol_type) hashtbl;
          defineds  : (string, term * hol_type option) hashtbl;
          uis       : (string, hol_type) hashtbl;
}

type symbol_class = FixedBT | Typevar | FixedLogicalSymbol | DefinedSymbol | UISymbol

let bt_i = basetype "$i"
let bt_o = basetype "$o"
let bt_type = basetype "$tType"

let interpreted_constants = ["$true";"$false";"~";"|";"~|";"&";"~&";"=>";"<=";"<=>";"<~>";"=";"!=";"?";"!";"!!";"??";"#box";"#dia"]
let ctrue = "$true"
let cfalse = "$false"
let neg = "~"
let box = "#box"
let diamond = "#dia"
let forall = "!"
let disjunction = "|"
let equality = "="

(* TODO: type variables must be handled correctly *)
let bt_x = basetype "X"

let poly0 = mk_polyvar 0

(* defined logical symbols: *)
let exists = "?"
let exists_def =
  Abstr(Symbol "P",abstr_type poly0 bt_o,
    Appl(Symbol neg,Appl(Symbol forall,
      Abstr(Symbol "X",poly0,
        Appl(Symbol neg,Appl(Symbol "P",Symbol "X"))))))
let quantifier_ty = abstr_type (abstr_type poly0 bt_o) bt_o

let forall_comb = "!!"
let exists_comb = "??"
let forall_comb_def = Symbol forall
let exists_comb_def = exists_def

let negated_disjunction = "~|"
let negated_disjunction_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(Symbol neg,
        Appl(
          Appl(Symbol disjunction,
            Symbol "X"),
          Symbol "Y"))))          
let negated_disjunction_ty = abstr_type bt_o (abstr_type bt_o bt_o)

let conjunction = "&"
let conjunction_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(Symbol neg,
        Appl(
          Appl(Symbol disjunction,
            Appl(Symbol neg, Symbol "X")),
          Appl(Symbol neg, Symbol "Y")))))
let conjunction_ty = abstr_type bt_o (abstr_type bt_o bt_o)

let negated_conjunction = "~&"
let negated_conjunction_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(Symbol neg,
        Appl(
          Appl(Symbol conjunction,
            Symbol "X"),
          Symbol "Y"))))          
let negated_conjunction_ty = abstr_type bt_o (abstr_type bt_o bt_o)


let implies = "=>" (* => *)
let implies_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(
        Appl(Symbol disjunction,
          Appl(Symbol neg, Symbol "X")),
        Symbol "Y")))
let implies_ty = abstr_type bt_o (abstr_type bt_o bt_o)

let i_f = "<=" (* <= *)
let i_f_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(
        Appl(Symbol disjunction,
          Symbol "X"),
        Appl(Symbol neg, Symbol "Y"))))
let i_f_ty = abstr_type bt_o (abstr_type bt_o bt_o)

let iff = "<=>" (* <=> *)
let iff_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(
        Appl(Symbol conjunction,
          Appl(
            Appl(Symbol implies, Symbol "X"),
            Symbol "Y")),
        Appl(
          Appl(Symbol implies, Symbol "Y"),
          Symbol "X"))))
let iff_ty = abstr_type bt_o (abstr_type bt_o bt_o)

let negated_iff = "<~>" (* <~> *)
let negated_iff_def =
  Abstr(Symbol "X", bt_o,
    Abstr(Symbol "Y", bt_o,
      Appl(Symbol neg,
        Appl(
          Appl(Symbol iff,
            Symbol "X"),
          Symbol "Y"))))   
let negated_iff_ty = abstr_type bt_o (abstr_type bt_o bt_o)


let nequals = "!=" (* != *)
let nequals_def =
  Abstr(Symbol "X", poly0,
    Abstr(Symbol "Y", poly0,
      Appl(Symbol neg,
        Appl(
          Appl(Symbol equality, Symbol "X"),
          Symbol "Y"))))
let nequals_ty = abstr_type poly0 (abstr_type poly0 bt_o)



let hashtbl_of_list ls =
  let ht = Hashtbl.create (length ls) in
  let _ = iter (fun (k,v) -> Hashtbl.add ht k v) ls in
  ht

let list_of_hashtbl ht =
  Hashtbl.fold (fun k v acc -> (k,v)::acc) ht []

let is_defined_logical_symbol s =
 List.mem s 
  [exists;
   negated_disjunction;
   conjunction;
   negated_conjunction;
   implies;
   i_f;
   iff;
   negated_iff;
   nequals;
   forall_comb;
   exists_comb]

let new_signature () = {
  basetypes = [bt_i; bt_o; bt_type];
  typevars  = ["X"];
  fixedlogs = hashtbl_of_list [
    (ctrue,       bt_o);
    (cfalse,      bt_o);
    (neg,         abstr_type bt_o bt_o);
    (box,         abstr_type bt_o bt_o);
    (diamond,     abstr_type bt_o bt_o);
    (forall,      abstr_type (abstr_type poly0 bt_o) bt_o);
    (disjunction, abstr_type bt_o (abstr_type bt_o bt_o));
    (equality,    abstr_type poly0 (abstr_type poly0 bt_o))];
  defineds  = hashtbl_of_list [
    (exists,      (exists_def,      Some quantifier_ty));
    (forall_comb, (forall_comb_def, Some quantifier_ty));
    (exists_comb, (exists_comb_def, Some quantifier_ty));
    (negated_disjunction, (negated_disjunction_def, Some negated_disjunction_ty));
    (conjunction, (conjunction_def, Some conjunction_ty));
    (negated_conjunction, (negated_conjunction_def, Some negated_conjunction_ty));
    (implies,     (implies_def,     Some implies_ty));
    (i_f,         (i_f_def,         Some i_f_ty));
    (iff,         (iff_def,         Some iff_ty));
    (negated_iff,         (negated_iff_def,         Some negated_iff_ty));    
    (nequals,     (nequals_def,     Some nequals_ty))];
  uis       = Hashtbl.create 10
}
  
  
let copy_signature sigma = {
  basetypes = sigma.basetypes;
  typevars  = sigma.typevars;
  fixedlogs = sigma.fixedlogs;
  defineds  = sigma.defineds;
  uis       = sigma.uis
}

let is_basetype_in sigma s = List.mem (basetype s) sigma.basetypes

let add_basetype sigma name = (* FIXME: use hashtable *)
  if not (is_basetype_in sigma name) then
    sigma.basetypes <- basetype name :: sigma.basetypes
  else failwith ("Type " ^ name ^ " is already declared in signature")

let add_type_var sigma name =
	if not (List.mem name sigma.typevars) (* FIXME: use hashtable *)
	then sigma.typevars <- name :: sigma.typevars

let add_defined_symbol ?(ty=None) sigma name t =
  if Hashtbl.mem sigma.defineds name 
  then failwith ("\nsymbol "^name^ " defined twice in THF problem")
  else
    Hashtbl.add sigma.defineds name (t,ty)

let defined_symbol_set_type sigma name ty =
  try (
    let (t,_) = Hashtbl.find sigma.defineds name in
    Hashtbl.replace sigma.defineds name (t,Some ty))
  with Not_found -> failwith "defined_symbol_set_type: unknown symbol"

let add_uninterpreted_symbol sigma name ty =
  if Hashtbl.mem sigma.uis name
  then failwith ("add_uninterpreted_symbol: duplicate definition of symbol "^name^
                 " with types "^(Hol_type.to_string (Hashtbl.find sigma.uis name))^
                 " and "^(Hol_type.to_string ty))
  else Hashtbl.add sigma.uis name ty

let addifnew_uninterpreted_symbol sigma name ty =
  if not (Hashtbl.mem sigma.uis name)
  then Hashtbl.add sigma.uis name ty

let is_defined_symbol sigma name =
  Hashtbl.mem sigma.defineds name

let is_fixed_logical_symbol sigma name =
  Hashtbl.mem sigma.fixedlogs name

let is_uninterpreted_symbol sigma name =
  Hashtbl.mem sigma.uis name

let get_defined_symbol sigma name =
  try (
    match Hashtbl.find sigma.defineds name with
      (t,_) -> t)
  with Not_found -> failwith "get_defined_symbol: unknown symbol"


let all_fixed_basetypes sigma =
  sigma.basetypes

(*excludes $i, $o, and $tType*)
let problemsupplied_fixed_basetypes sigma =
  List.filter (fun ty -> ty <> bt_i && ty <> bt_o && ty <> bt_type) sigma.basetypes

let all_type_vars sigma =
  sigma.typevars


let all_fixed_logical_symbols sigma =
  list_of_hashtbl sigma.fixedlogs


let all_defined_symbols sigma =
  list_of_hashtbl sigma.defineds

let all_defined_symbols_without_logical_symbols sigma =
  let list = all_defined_symbols sigma in 
  let (_,non_logical) =
    List.partition (fun (s,t) -> is_defined_logical_symbol s) list in
  non_logical


let all_uninterpreted_symbols sigma =
  list_of_hashtbl sigma.uis

let class_of_symbol sigma name =
  if name = Hol_type.dest_basetype bt_i || name = Hol_type.dest_basetype bt_o then
    Some FixedBT
  else if Hashtbl.mem sigma.fixedlogs name then
    Some FixedLogicalSymbol
  else if Hashtbl.mem sigma.defineds name then
    Some DefinedSymbol
  else if Hashtbl.mem sigma.uis name then
    Some UISymbol
  else if mem name sigma.typevars then
    Some Typevar
  else None

let type_of_symbol sigma name =
  try Hashtbl.find sigma.fixedlogs name
  with Not_found ->
    try (
      let (_,tyo) = Hashtbl.find sigma.defineds name in
      match tyo with
          Some ty -> ty
        | None -> failwith "type_of_symbol: type unknown"
    )
    with Not_found ->
      try Hashtbl.find sigma.uis name
      with Not_found ->
        failwith "type_of_symbol: unknown symbol"


(* signature names to hotptp names *)
let hotptpsymb = function
          "~" -> "~"
	| "|"  -> "|"
	| "&" -> "&"
	| "~|" -> "~|"
	| "~&" -> "~&"
	| "=" -> "="
	| "!=" -> "!="
	| "=>" -> "=>"
	| "<=" -> "<="
	| "<=>" -> "<=>"
	| "<~>" -> "<~>"
	| "?" -> "?"
	| "!" -> "!"
  | "??" -> "??"
  | "!!" -> "!!"
        | "@+" -> "@+"
        | "@-" -> "@-"
(* habe forall und exists noch hinzugefuegt. Chris *)
        | s -> s
(*	| s -> failwith "unknown symbol" 
        Mayhem!! Soll in term.ml Failure produzieren, wird hier aber nicht aufgefangen.
        Hab's in term.ml umbenannt, hoffe das haut dann so hin. Frank *)

let compare_defns (s1, (t1, ty1_opt)) (s2, (t2, ty2_opt)) =
  let s_comp = String.compare s1 s2
  in
    if s_comp <> 0 then s_comp
    else
      let t_comp = Term.compare t1 t2
      in
        if t_comp <> 0 then t_comp
        else
          match (ty1_opt, ty2_opt) with
              (None, None) -> 0
            | (None, _) -> -1
            | (Some ty1, Some ty2) -> Hol_type.compare ty1 ty2
            | (Some _, None) -> 1

(** This function should go to module signature *)
let signature_to_string (sigma:signature) =
  let base_types_string = fold_left (fun s i -> (s^"\n  "^(Hol_type.to_hotptp i))) "" (sort Hol_type.compare (all_fixed_basetypes sigma)) in
  let type_variables_string = fold_left (fun s i -> (s^"\n  "^i)) "" (sort String.compare (all_type_vars sigma)) in
  let fixed_logical_symbols_string = fold_left (fun s (t,i) -> (s^"\n  "^t^" ("^(hotptpsymb t)^") "^": "^(Hol_type.to_hotptp i))) "" (sort Hol_type.compare_string_type_pair (all_fixed_logical_symbols sigma)) in
  let defined_symbols_string = fold_left (fun s (t,(d,i)) -> (s^"\n  "^t^" ("^(hotptpsymb t)^") "^": "^(Term.to_hotptp d))) "" (sort compare_defns (all_defined_symbols sigma)) in
  let uninterpreted_symbols_string = fold_left (fun s (t,i) -> (s^"\n  "^t^": "^(Hol_type.to_hotptp i))) "" (sort Hol_type.compare_string_type_pair (all_uninterpreted_symbols sigma)) in
  "\n <base types> "^base_types_string^
  "\n <type variables> "^type_variables_string^
  "\n <fixed logical symbols> "^fixed_logical_symbols_string^
  "\n <symbol types (upper case: free variables; lower case: constants)> "^uninterpreted_symbols_string^
  "\n <defined symbols> "^defined_symbols_string^"\n"

let symbol_types_to_thf (sigma:signature) =
  let type_concat s (t, i) =
    if (Str.string_match (Str.regexp "[A-Z].*") t 0) ||
      (Str.string_match (Str.regexp "[0-9].*") t 0) then s
    else s ^ "\n thf(tp_" ^ t ^ ",type,(" ^ t ^ ": " ^ Hol_type.to_hotptp i ^ "))." in
  let type_info_string symbols =
    fold_left type_concat  "" (sort Hol_type.compare_string_type_pair symbols) in
  let basetypes =
    map (fun ty -> (Hol_type.to_string ty, bt_type)) (problemsupplied_fixed_basetypes sigma)
  in
    type_info_string basetypes ^
    type_info_string (all_uninterpreted_symbols sigma)

let defs_to_thf (sigma:signature) (origfilename:string) =
  let defined_symbols_string = fold_left (fun s (t,(d,i)) -> (s^"\n thf("^t^",definition,("^t^" = ("^(Term.to_hotptp d)^")),file(\'"^origfilename^"\',"^t^")).")) "" (sort compare_defns (all_defined_symbols_without_logical_symbols sigma)) in
   defined_symbols_string

let all_defs_names (sigma:signature) =
  let defs_string = fold_left (fun s (t,(d,i)) -> (s^","^t)) "" (sort compare_defns (all_defined_symbols_without_logical_symbols sigma)) in
   defs_string


