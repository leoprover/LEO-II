(* ========================================================================= *)
(* User readable terms                                                       *)
(* ========================================================================= *)

open Hol_type
open Util
(* open Signature *)

(*FIXME move this elsewhere*)
exception PARSER

(** the user-readable terms have a simple structure which should not
    be hidden in an ADT.
    The insertion into the termset is easier to implement if the term
    structure is public. *)
    
type term =
  Symbol of string |
  Appl of term * term |
  Abstr of term * hol_type * term

let alpha_equiv t1 t2 =
  let rec alpha_equiv' bnd_eqs t1 t2 =
    match (t1, t2) with
        (Symbol x, Symbol y) ->
          if List.mem_assoc x bnd_eqs then List.assoc x bnd_eqs = y else x = y
      | (Abstr (Symbol x, ty1, t1'),
         Abstr (Symbol y, ty2, t2')) ->
          ty1 = ty2 && alpha_equiv' ((x, y) :: bnd_eqs) t1' t2'
      | (Appl (t1, t2),
         Appl (t1', t2')) ->
          alpha_equiv' bnd_eqs t1 t1' && alpha_equiv' bnd_eqs t2 t2'
      | _ -> false
  in alpha_equiv' [] t1 t2

let rec term_weighting t =
  match t with
      Symbol _ -> 1
    | Appl (t1, t2) -> term_weighting t1 + term_weighting t2
    | Abstr (_, ty, t') -> 1 + Hol_type.type_ordering ty + term_weighting t'

let compare t1 t2 =
  let w1 = term_weighting t1 in
  let w2 = term_weighting t2
  in
    if w1 = w2 then 0
    else if w1 < w2 then -1
    else 1

let is_symbol = function
    Symbol _ -> true
  | _ -> false

let is_variable = function
    Symbol s -> (String.get s 0) >= 'A' && (String.get s 0) <= 'Z'
    (*Symbol s -> Char.uppercase (String.get s 0) = String.get s 0*)
  | _ -> false
  
let get_symbol = function
    Symbol s -> s
  | _ -> failwith "not a symbol"
  
let is_appl = function
    Appl _ -> true
  | _ -> false
  
let is_abstr = function
    Abstr _ -> true
  | _ -> false  

(*
let free_vars t =
  let bound = Hashtbl.create 10 in
  let rec free = function
      Symbol s as t ->
        if Hashtbl.mem bound s then []
	else if is_variable t then [s]
	else []
    | Appl(t1,t2) ->
        concat_unique (free t1) (free t2)
    | Abstr(x,_,t1) ->
        assert(is_symbol x);
        let _ = Hashtbl.add bound (get_symbol x) () in
	free t1
  in free t
*)


let free_vars t =
  let rec free bound t =
    match t with 
	Symbol s ->
          if List.mem s bound then []
	  else if is_variable t then [s]
	  else []
      | Appl(t1,t2) ->
          concat_unique (free bound t1) (free bound t2)
      | Abstr(x,_,t1) ->
          assert(is_symbol x);
          let newbound = (get_symbol x)::bound in
	    free newbound t1
  in free [] t


let term_symbols t =
  let bound = Hashtbl.create 10 in
  let rec help = function
      Symbol s as t ->
        if Hashtbl.mem bound s then []
	else if is_symbol t then [s]
	else []
    | Appl(t1,t2) ->
        concat_unique (help t1) (help t2)
    | Abstr(_,_,t1) ->
    	help t1
  in help t

let rec get_head_symbol = function
    Symbol s -> Symbol s
  | Abstr(x,_,t1) -> get_head_symbol t1
  | Appl(t1,t2) -> get_head_symbol t1


(** pretty printer. This is not very sophisticated -- "to_hotptp"*)
let rec to_string = function
    Symbol s -> s
  | Appl(Appl(Symbol s,t1),t2)
     when s = "=" || s = "|" || s = "&" || s = "=>" || s = "<=>" || s = "<=" ->
      "(" ^ add_pars t1 ^ " = " ^ add_pars t2 ^ ")"
  | Appl(t1,t2) -> add_pars t1 ^ " " ^ add_pars t2
  | Abstr(x,ty,t) -> "^ [" ^ to_string x ^ ":" ^ Hol_type.to_string ty ^ "]: "^(to_string t)
and add_pars t =
  if is_symbol t then to_string t
  else "("^(to_string t)^")"

let symboltype gamma s =
  try (gamma s)
  with Failure _ -> new_typevar ()

let empty _ = failwith "empty"
let adjoin gamma v t = fun x -> if x=v then t else gamma x

let type_of sigma t =
  let rec typeof gamma = function
      (*Symbol s -> symboltype gamma s*)
      Symbol s -> (try (gamma s) with Failure _ -> failwith ("type of symbol "^s^" unknown"))
    | Abstr(x,ty,t') ->
        let ty' = typeof (adjoin gamma (get_symbol x) ty) t' in
        abstr_type ty ty'
    | Appl(t1,t2) ->
        let ty1 = typeof gamma t1 in
        let ty2 = typeof gamma t2 in
        if is_funtype ty1 then
          let (ty11,ty12) = (arg_type ty1,result_type ty1) in
          if ty11=ty2 then ty12
          else
            let theta = decompose_constraint (ty11,ty2) in
            try
              substs theta ty12
            with _ -> failwith ("argument type mismatch: "^(to_string t1)^" of type "^(Hol_type.to_string ty1)^
              " applied to "^(to_string t2)^" of type "^(Hol_type.to_string ty2))
        else failwith ("applying a non-function: "^(to_string t1)^" of type "^(Hol_type.to_string ty1)^
              " applied to "^(to_string t1)^" of type "^(Hol_type.to_string ty1))
  in try typeof sigma t with
      Failure s ->
        begin
          Util.sysout 0 ("\nHallo: " ^ s);
          failwith (" in term " ^ to_string t ^ ":\n" ^ s)
        end

let rec all_arg_terms_up_to_term t gt = 
  if t = gt then (true,[])
  else 
    match t with
       Symbol s -> (false,[])
     | Abstr(var,ty,body) -> (false,[])
     | Appl(hd,arg) -> 
	 let (flag,tl) = all_arg_terms_up_to_term  hd gt in
	 (flag,tl@[arg])

let types_of_all_arg_terms_up_to_term t gt sigma = 
  let (flag,termlist) = (all_arg_terms_up_to_term t gt) in
 (flag,(List.map (fun term -> type_of sigma term) termlist)) 


let bvar_count = ref 0

let new_bvarname () = 
  let var = "SY"^(string_of_int !bvar_count) in
  bvar_count := !bvar_count + 1;
  var

let bn_flag = ref false

let rec var_rename v1 v2 t =
  match t with
    Symbol s -> if s = v1 then Symbol v2 else t
  | Appl(t1,t2) -> Appl(var_rename v1 v2 t1, var_rename v1 v2 t2)
  | Abstr(Symbol v,ty,t1) -> if v = v1 then t else Abstr(Symbol v,ty,var_rename v1 v2 t1)
  | _ -> failwith "Beta_normalize failed"

let rec bn bound t =
  Util.sysout 3 ("\n bn \n  :bound: "^(List.fold_right (fun (s,t) rs -> s^"/"^(to_string t)^" "^rs) bound "")^"\n  :t: "^(to_string t));
  let t_new= (
  match t with
    Symbol s ->
        if List.mem_assoc s bound then
        (bn_flag := true;
         List.assoc s bound)
      else Symbol s
  | Appl(Abstr(Symbol x,_,t1),t2) ->
      bn_flag := true;
      let t_new = bn ((x, bn bound t2)::bound) t1 in
      t_new
  | Appl(t1,t2) -> 
      let t1_new = bn bound t1 in
      (match t1_new with
         Abstr(Symbol x,_,t3) -> 
           bn_flag := true;
           (* bn ((x, bn bound t2)::bound) t3 *)
           bn bound (Appl(t1_new,t2))
       | _ -> Appl(t1_new, bn bound t2))
  | Abstr(Symbol v,ty,t1) ->
      let nv = new_bvarname () in
      let bn_flag_now = !bn_flag in
      (* let t1_renamed = bn [(v,Symbol nv)] t1 in *)
      let t1_renamed = var_rename v nv t1 in
      bn_flag := false;
      let t1_subst = bn bound t1_renamed in
      let t_new = (
      if !bn_flag
      then Abstr(Symbol nv,ty,t1_subst)
      else (bn_flag := bn_flag_now; t)
      ) in
      t_new

  | _ -> failwith "Beta_normalize failed")
  in
  (* print_string ("-> "^(to_string t_new)^"\n"); *)
  t_new

let beta_normalize = bn []





let subst_symbols = bn








let multi_abstr args body =
  List.fold_right (fun (x,ty) acc -> Abstr(Symbol x, ty, acc)) args body

let multi_quantified quantifier args body =
  List.fold_right (fun (x,ty) acc -> Appl(quantifier,Abstr(Symbol x, ty, acc))) args body

let de_multi_abstr t =
	let rec chip acc = function
	    Abstr(Symbol x, ty, body) -> chip ((x,ty)::acc) body
	  | t' -> (List.rev acc, t') in
	chip [] t

let de_multi_quantified t =
	let rec chip quantifier acc = function
	    Appl(quantifier',Abstr(Symbol x, ty, body)) as t' ->
	      if quantifier = quantifier' then chip quantifier ((x,ty)::acc) body
	      else (quantifier, List.rev acc, t')
	  | t' -> (quantifier, List.rev acc, t') in
	match t with
	  Appl(Symbol q as quantifier,func) ->
	    if q = "!" || q = "?" then chip quantifier [] t
	    else failwith "no quantifier found"
	| _ -> failwith "no quantifier found"
	
  
  


let lstapp acc el =
	acc^(if acc="" then "" else ",")^el

(* signature names to hotptp names *)
let hotptpsymb_critical = function
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

  | s -> failwith "unknown symbol"
	


(** printing to THF *)

let rec to_hotptp = function
    Symbol s -> (
				match s with
					"$true" -> "$true"
				| "$false" -> "$false"
				| _ -> s)
	| Appl(Symbol "!", Abstr(_,_,_)) as t ->
	    Util.sysout 3 "\n Enter hier";
	    Util.sysout 3 ("\n Printing: "^(to_string t)^"\n");
	    let res =
	      let (_,args,body) = de_multi_quantified t in 
	        Util.sysout 3 ("\n Body: "^(to_string body)^"\n");
		"!["^(List.fold_left
			  (fun acc (x,ty) -> lstapp acc	(x^":"^(Hol_type.to_hotptp ty)))
			  "" args)^"]: "^(add_pars body)
	    in (Util.sysout 3 "\n Leave hier"; res)
	| Appl(Symbol "?", Abstr(_,_,_)) as t ->
				let (_,args,body) = de_multi_quantified t in
				"?["^(List.fold_left
					(fun acc (x,ty) -> lstapp acc	(x^":"^(Hol_type.to_hotptp ty)))
					"" args)^"]: "^(add_pars body)
  | Appl(Symbol ("!!" as c), t')
  | Appl(Symbol ("??" as c), t') -> c ^ " @ " ^ add_pars t'
  | Abstr(_,_,_) as t ->
				let (args,body) = de_multi_abstr t in
				"^["^(List.fold_left
					(fun acc (x,ty) -> lstapp acc	(x^":"^(Hol_type.to_hotptp ty)))
					"" args)^"]: "^(add_pars body)
  | Appl(Appl(Symbol binop, t1),t2) -> (
			try ((add_pars t1)^" "^(hotptpsymb_critical binop)^" "^(add_pars t2))
			with _ -> "("^binop^"@"^(add_pars t1)^")@"^(add_pars t2)) (* FIXME: will not print correctly Appl(Appl(Symbol "~", t1),t2) *)
  | Appl(Symbol unop,t) -> (
			try ((hotptpsymb_critical unop)^" ("^(to_hotptp t)^")")
			with _ -> unop^"@"^(add_pars t))
  | Appl(t1,t2) ->
  		(add_pars t1)^"@"^(add_pars t2)
and add_pars t =
  if is_symbol t then to_hotptp t
  else "("^(to_hotptp t)^")"


let rec to_compressed = function
    Symbol s -> s
  | Appl(Symbol "!", _) as t ->
        let (_,args,body) = de_multi_quantified t in
        "! ["^(List.fold_left
          (fun acc (x,ty) -> lstapp acc (x^":"^(Hol_type.to_hotptp ty)))
          "" args)^"] : "^(add_pars body)
  | Appl(Symbol "?", _) as t ->
        let (_,args,body) = de_multi_quantified t in
        "? ["^(List.fold_left
          (fun acc (x,ty) -> lstapp acc (x^":"^(Hol_type.to_hotptp ty)))
          "" args)^"] : "^(add_pars body)
  | Abstr(_,_,_) as t ->
        let (args,body) = de_multi_abstr t in
        "^ ["^(List.fold_left
          (fun acc (x,ty) -> lstapp acc (x^":"^(Hol_type.to_hotptp ty)))
          "" args)^"] : "^(add_pars body)
  | Appl(Appl(Symbol binop, t1),t2) -> (
      try ((add_pars t1)^(hotptpsymb_critical binop)^(add_pars t2))
      with _ -> "("^binop^" "^(add_pars t1)^") "^(add_pars t2)) (* FIXME: will not print correctly Appl(Appl(Symbol "neg", t1),t2) *)
  | Appl(Symbol unop,t) -> (
      try ((hotptpsymb_critical unop)^(add_pars t))
      with _ -> unop^" "^(add_pars t))
  | Appl(t1,t2) ->
      (add_pars t1)^" "^(add_pars t2)
and add_pars t =
  if is_symbol t then to_compressed t
  else "("^(to_compressed t)^")"



(** conversion in POST *)

									 
let postsymb_critical = function
    "~" -> "not"
  | "|"  -> "or"
  | "&" -> "and"
  | "~|" -> failwith "unknown post representation"
  | "~&" -> failwith "unknown post representation"
  | "=" -> "="
  | "!=" -> failwith "unknown post representation"
  | "=>" -> "implies"
  | "<=" -> failwith "unknown post representation"
  | "<=>" -> "equiv"
  | "<~>" -> failwith "unknown post representation"
  | "!" -> failwith "unknown post representation"
  | "?" -> failwith "unknown post representation"
  | s -> failwith "unknown symbol"



let rec to_post = function
    Symbol s -> 
      (match s with
	"$true" -> "true"
      | "$false" -> "false"
      | _ -> s)
  | Appl(Symbol "!",Abstr(Symbol x, ty, body)) -> 
      "(forall (lam ("^x^" "^(Hol_type.to_post ty)^") "^(to_post body)^"))"
  | Appl(Symbol "?",Abstr(Symbol x, ty, body)) -> 
      "(exists (lam ("^x^" "^(Hol_type.to_post ty)^") "^(to_post body)^"))"
  | Abstr(_,_,_) as t ->
      let (args,body) = de_multi_abstr t in
      ((List.fold_left (fun acc (x,ty) -> ("(lam ("^x^" "^(Hol_type.to_post ty)^") ")) "" args)
       ^(to_post body)^")")
  | Appl(Appl(Symbol binop, t1),t2) -> (
      try "("^(postsymb_critical binop)^" "^(to_post t1)^" "^(to_post t2)^")"
      with _ -> "("^binop^" "^(to_post t1)^" "^(to_post t2)^")"
     )
  | Appl(Symbol unop,t) -> (
      try "("^(postsymb_critical unop)^" "^(to_post t)^")"
      with _ -> "("^unop^" "^(to_post t)^")"
     )
  | Appl(t1,t2) ->
      "("^(to_post t1)^" "^(to_post t2)^")"

let termlist_to_string (ts:term list) =
  "["^(List.fold_left (fun s t -> (s^(to_post t)^" ")) " " ts)^"]"


let smaller_head t1 t2 =
  let res = String.compare (to_string (get_head_symbol t1)) (to_string (get_head_symbol t2))
  in
    Util.sysout 3 ("\n t1: "^(to_string t1));
    Util.sysout 3 ("\n t1: "^(to_string t2));
    Util.sysout 3 ("\n res: "^(string_of_int res));
    res <= 0
