(* ========================================================================= *)
(* HOL Types                                                                 *)
(* ========================================================================= *)

open Util
open List

let tyvar_counter = ref 0

type hol_type =
    Basetype of string
  | Funtype of hol_type * hol_type


let basetype name =
  Basetype(name)

let abstr_type argtype bodytype =
  Funtype(argtype,bodytype)


let new_typevar() =
  let x = !tyvar_counter in
  tyvar_counter := !tyvar_counter + 1;
  basetype ("X"^(string_of_int x))

(* 0 -> 'A, 1 -> 'B, ... 26 -> 'A1 etc. *)
let mk_polyvar i =
  let m = i / 26 in
  if m=0 then Basetype ("'"^(String.make 1 (Char.chr (65+i))))
  else Basetype ("'"^(String.make 1 (Char.chr (65+(i mod 26))))^(string_of_int m))


let dest_basetype = function
    Basetype s -> s
  | _ -> failwith "dest_basetype"

let dest_funtype = function
    Funtype (t1, t2) -> (t1, t2)
  | _ -> failwith "dest_funtype: argument not a function type"

let appl_type funtype argtype =
  match funtype with
      Funtype(type1,type2) ->
        assert(type1=argtype);
        type2
    | _ -> failwith "appl_type: first argument not a function type"


let arg_type = function
    Funtype(argtype,_) -> argtype
  | _ -> failwith "arg_type: argument not a function type"


let result_type = function
    Funtype(_,restype) -> restype
  | _ -> failwith "arg_type: argument not a function type"


let rec all_arg_types' ls = function
    Funtype(argtype,restype) -> all_arg_types' (argtype::ls) restype
  | Basetype _ -> ls

let all_arg_types t = List.rev (all_arg_types' [] t)


let rec base_result_type = function
    Basetype s -> Basetype s
  | Funtype(type1,type2) -> base_result_type type2

let rec mk_funtype list_of_arg_types goal_type =
  match list_of_arg_types with
     []  -> goal_type
   | hd::tl -> Funtype(hd,(mk_funtype tl goal_type))


let is_funtype = function
    Funtype _ -> true
  | _  -> false


let is_basetype = function
    Basetype _ -> true
  | _ -> false

let is_polyvar = function
    Basetype s ->
      let rest = String.sub s 1 (String.length s - 1) in
      (String.get s 0 = '\'' && (String.uppercase rest = rest)) || (s = "*") || (String.uppercase s = s)
  | Funtype _ -> false

let is_typevar = function
    Basetype s as ty -> not (is_polyvar ty || s="$o"(*FIXME const*) || s="$i"(*FIXME const*) || s = "$tType"(*FIXME const*)) (* HACK! We should look at signature. *)
  | Funtype _ -> false


let is_applicable type1 type2 =
  match type1 with
      Funtype(argtype,_) -> type2=argtype
    | _ -> false


let rec get_typevars is_typevar = function
   Basetype s as ty -> if is_typevar ty then [s] else []
 | Funtype(ty1,ty2) -> concat_unique (get_typevars is_typevar ty1) (get_typevars is_typevar ty2)


let rec get_polyvars = function
    Basetype s as ty -> if is_polyvar ty then [s] else []
  | Funtype(ty1,ty2) -> concat_unique (get_polyvars ty1) (get_polyvars ty2)


let rec rename_polyvar x vars =
  let numstr = String.sub x 2 (String.length x -2) in
  let num = (if String.length numstr = 0 then 0 else int_of_string numstr) in
  if List.mem x vars then rename_polyvar ((String.sub x 0 2)^(string_of_int (num+1))) vars
  else x


let rec to_string = function
    Basetype s -> s
  | Funtype(ty1,ty2) -> (add_pars ty1)^">"^(add_pars ty2)
and add_pars ty =
  if is_basetype ty then to_string ty
  else "("^(to_string ty)^")"

let rec to_fotptp_cnf = function
    Basetype s -> Util.clean_symbol s
  | Funtype(ty1,ty2) -> (add_pars ty1)^""^(add_pars ty2)
and add_pars ty =
  if is_basetype ty then to_fotptp_cnf ty
  else "T"^(to_fotptp_cnf ty)^"T"


let rec all_arg_types_up_to_goal_type t gt =
  Util.sysout 3 ("\n all_arg_types_up_to_goal_type: "^(to_string t)^" "^(to_string gt));
  if t = gt then (true,[])
  else
    match t with
       Basetype s -> if t = gt then (true,[]) else (false,[])
     | Funtype(argtype,restype) ->
	 let (flag,tl) = all_arg_types_up_to_goal_type restype gt in
	 (flag,argtype::tl)



let rec subst ty x ty' =
  match ty with
      Basetype s -> if s=x then ty' else ty
    | Funtype(ty1,ty2) -> Funtype(subst ty1 x ty',subst ty2 x ty')


(* assumes theta is in solved form, i.e. idempotent *)
let substs theta ty =
  List.fold_left (fun acc (x,ty') -> subst acc x ty') ty theta


let substC x ty' c =
  List.map (fun (ty1,ty2) -> (subst ty1 x ty', subst ty2 x ty')) c

let substC_rhs x ty' c =
  List.map (fun (ty1,ty2) -> (subst ty1 x ty',ty2)) c

let decompose_constraint c =
  let rec decompose cdone ctodo =
    match ctodo with
        [] -> cdone
      | ((ty1,ty2)::cr) ->
          if ty1=ty2 then decompose cdone cr else
          match (ty1,ty2) with
              (Funtype(ty11,ty12),Funtype(ty21,ty22)) ->
              decompose cdone ((ty11,ty21)::(ty12,ty22)::cr)
            | _ ->
              if is_polyvar ty1 then
                let x=dest_basetype ty1 in
                decompose ((ty1,ty2)::(substC_rhs x ty2 cdone)) (substC_rhs x ty2 cr)
              else if is_polyvar ty2 then
                decompose cdone ((ty2,ty1)::cr)
              else failwith ("unsatisfiable: "^(to_string ty1)^" := "^(to_string ty2))
  in
    map (fun (ty1,ty2) -> (dest_basetype ty1, ty2)) (decompose [] [c])

let rec occurs x = function
    Basetype s -> s=x
  | Funtype(ty1,ty2) -> occurs x ty1 || occurs x ty2

(* apply a substitution to a list of equations *)
let substC c x ty =
  List.map (fun (ty1,ty2) -> (subst ty1 x ty,subst ty2 x ty)) c

exception Unsatisfiable

let unify_constraints is_polytypevar constraints =
  let rec unify' cdone ctodo =
    match ctodo with
        [] -> cdone
      | ((ty1,ty2)::c) ->
        if ty1=ty2 then unify' cdone c else
          match (ty1,ty2) with
  	      (Funtype(ty11,ty12),Funtype(ty21,ty22)) ->
	      unify' cdone ((ty11,ty21)::(ty12,ty22)::c)
	    | _ ->
	      if is_polytypevar ty1 && is_typevar ty2 && not (is_polytypevar ty2) then
	        unify' cdone ((ty2,ty1)::c)
	      else if is_typevar ty1 then
	        let x = dest_basetype ty1 in
	        if occurs x ty2 then (* raise Unsatisfiable *) (print_string "Warning: Unsatisfiable Type!\n";[])
	        else unify' ((ty1,ty2)::(substC cdone x ty2)) (substC c x ty2)
	      else if is_typevar ty2 then
	        unify' cdone ((ty2,ty1)::c)
	      else (* raise Unsatisfiable *) (print_string "Warning: Unsatisfiable Type!\n";[])
  in unify' [] constraints




open List

let inst_polyvars ty =
  let repl = ref [] in
  let rec inst = function
      Basetype s as ty' ->
        if is_polyvar ty' then
	  if mem_assoc s !repl
	  then Basetype (assoc s !repl)
	  else let tv = new_typevar () in
	    let _ = repl := (s,dest_basetype tv)::!repl in
	    tv
	else ty'
    | Funtype(ty1,ty2) ->
        let ty1' = inst ty1 in
	let ty2' = inst ty2 in
	Funtype(ty1',ty2')
  in
    let ty' = inst ty in
    (ty',rev(snd(split !repl)))

let uninst_polyvars (ty : hol_type) (vl : string list) : hol_type =
  let replinv = combine vl (Util.iteri id (length vl)) in
  let rec uninst = function
      Basetype s as ty' ->
        if mem_assoc s replinv
	then mk_polyvar (assoc s replinv)
	else ty'
    | Funtype(ty1,ty2) ->
        let ty1' = uninst ty1 in
	let ty2' = uninst ty2 in
	Funtype(ty1',ty2')
  in uninst ty


let minimize_polyvars ty =
  uninst_polyvars ty (get_polyvars ty)

let rec to_hotptp = function
    Basetype s -> s
  | Funtype(ty1,ty2) -> ("("^(to_hotptp ty1)^">"^(to_hotptp ty2)^")")

let rec to_post = function
    Basetype s -> (
      match s with
    	"i" -> "i"
      | "o" -> "o"
      | "$i" -> "$i"
      | "$o" -> "$o"
      | _ -> s
     )
  | Funtype(ty1,ty2) -> "("^(to_post ty2)^" "^(to_post ty1)^")"

let rec rk' ty =
  if is_typevar ty || is_polyvar ty
  then 0 else
    match ty with
      Basetype s -> if s = "$o" (*FIXME const*) then 1 else 0
    | Funtype(ty1,ty2) -> rk' ty1 + rk' ty2 + 1

let rec type_ordering = function
    Basetype _ -> 0
  | Funtype(ty1,ty2) -> rk' ty1 + type_ordering ty2

let compare ty1 ty2 =
  let ord1 = type_ordering ty1 in
  let ord2 = type_ordering ty2
  in
    if ord1 = ord2 then 0
    else if ord1 < ord2 then -1
    else 1

let compare_string_type_pair (s1, ty1) (s2, ty2) =
  let s_comp = String.compare s1 s2
  in if s_comp = 0 then compare ty1 ty2 else s_comp
