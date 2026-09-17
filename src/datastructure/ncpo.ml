(* ========================================================================= *)
(* A computability path order for LEO-II's terms                             *)
(* ========================================================================= *)

(* See ncpo.mli for what this is and for the two cautions that come with it. *)

open Hol_type
open Term

type status = Lex | Mul

type verdict = Greater | Less | Equal | Incomparable

type params = {
  sort_prec : string -> int;
  const_prec : string -> int;
  status : string -> status;
  typing : string -> hol_type;
  type_check : bool;
}

let default_params typing = {
  sort_prec = (fun _ -> 0);
  const_prec = Hashtbl.hash;
  status = (fun _ -> Lex);
  typing = typing;
  type_check = true;
}

(* ------------------------------------------------------------------ *)
(* The companion order on types                                       *)
(* ------------------------------------------------------------------ *)

let rec type_gt sp t1 t2 =
  (* a function type dominates its own result type, transitively *)
  (match t1 with
       Funtype (_, r1) -> r1 = t2 || type_gt sp r1 t2
     | _ -> false)
  ||
  (* right congruence, and the sort precedence at the leaves *)
  (match (t1, t2) with
       (Funtype (a1, r1), Funtype (a2, r2)) -> a1 = a2 && type_gt sp r1 r2
     | (Basetype a, Basetype b) -> sp a > sp b
     | _ -> false)

let type_ge sp t1 t2 = t1 = t2 || type_gt sp t1 t2

(* ------------------------------------------------------------------ *)
(* Terms                                                              *)
(* ------------------------------------------------------------------ *)

(* Fresh names for the variables that opening an abstraction introduces.  They
   are confined to one comparison: nothing outside this module ever sees them,
   and they carry a character no parsed symbol can carry. *)
let fresh_counter = ref 0
let fresh_var () =
  incr fresh_counter;
  "Ncpo#" ^ string_of_int !fresh_counter

(* head symbol and arguments, in application order *)
let rec head_args t acc =
  match t with
      Appl (t1, t2) -> head_args t1 (t2 :: acc)
    | _ -> (t, acc)

let dest_flat t = head_args t []

(* Open an abstraction on a given fresh name. *)
let open_abstr_on z t =
  match t with
      Abstr (Symbol v, ty, body) -> (ty, subst_symbols [(v, Symbol z)] body)
    | Abstr (_, ty, body) -> (ty, body)
    | _ -> raise (Invalid_argument "Ncpo.open_abstr_on")

(* The auxiliary variable set of the published definition, carried with the
   types of its members so that the type check can still be answered inside a
   binder. *)
let ty_of p aux t =
  try Some (type_of (fun s -> try List.assoc s aux with Not_found -> p.typing s) t)
  with _ -> None

let types_ok p aux s t =
  if not p.type_check then true
  else
    match (ty_of p aux s, ty_of p aux t) with
        (Some tys, Some tyt) -> type_ge p.sort_prec tys tyt
      | _ -> false                  (* a type we cannot compute refuses the pair *)

(* The measure |s| + |t| strictly decreases at every recursive call below, so
   the mutual recursion terminates. *)
let rec ncpo p level aux s t =
  types_ok p aux s t && dispatch_on_s p level aux s t

and dispatch_on_s p level aux s t =
  match s with
      Abstr (_, _, _) -> lam_head p level aux s t
    | _ ->
        let (h, sargs) = dest_flat s in
        (match h with
             Symbol f when not (is_variable h) -> const_head p level aux s f sargs t
           | _ ->
               (* No rule makes a term with a variable or redex head greater
                  than anything: the order never orients out of a flex term,
                  which is what keeps it stable under substitution. *)
               false)

and const_head p level aux s f sargs t =
  (* the term is one of the variables a lambda-opening on the right introduced *)
  (match t with Symbol z -> List.mem_assoc z aux | _ -> false)
  (* an argument of s already dominates t; accessibility is left at "all" *)
  || List.exists (fun si -> alpha_equiv si t || ncpo p 1 aux si t) sargs
  || (match t with
          Abstr (_, _, _) ->
            (* open t and carry the fresh variable in the auxiliary set *)
            let z = fresh_var () in
            let (tyz, tbody) = open_abstr_on z t in
              ncpo p level ((z, tyz) :: aux) s tbody
        | _ ->
            let (g, targs) = dest_flat t in
              (match g with
                   Symbol gn when is_variable g ->
                     (* a variable head is dominated only when it is one of the
                        opened variables; a genuine free variable could be
                        instantiated with anything, so the pair stays unoriented *)
                     level = 1 && targs <> [] && List.mem_assoc gn aux
                     && List.for_all (fun u -> ncpo p 1 aux s u) targs
                 | Symbol gn ->
                     let rf = p.const_prec f and rg = p.const_prec gn in
                       if rf > rg then
                         List.for_all (fun u -> ncpo p 1 aux s u) targs
                       else if rf = rg && p.status f = p.status gn then
                         (match p.status f with
                              Lex -> lex_gt p aux sargs targs
                            | Mul -> mul_gt p aux sargs targs)
                         && List.for_all (fun u -> ncpo p 1 aux s u) targs
                       else false
                 | _ -> false))

and lam_head p level aux s t =
  let z = fresh_var () in
  let (tyz, sbody) = open_abstr_on z s in
  let aux' = (z, tyz) :: aux in
    (* the body of s already dominates t *)
    alpha_equiv sbody t || ncpo p level aux' sbody t
    || (match t with
            Abstr (_, _, _) ->
              (* align the binders, reusing the same fresh variable when the
                 two binder types agree *)
              let (tyt, _) = open_abstr_on z t in
                if tyt = tyz then
                  let (_, tbody) = open_abstr_on z t in
                    ncpo p level aux' sbody tbody
                else
                  let z' = fresh_var () in
                  let (tyz', tbody) = open_abstr_on z' t in
                    ncpo p level ((z', tyz') :: aux') sbody tbody
          | _ -> false)

and lex_gt p aux l1 l2 =
  match (l1, l2) with
      ([], []) -> false
    | (_, []) -> true
    | ([], _) -> false
    | (a :: r1, b :: r2) ->
        if alpha_equiv a b then lex_gt p aux r1 r2 else ncpo p 1 aux a b

and mul_gt p aux l1 l2 =
  (* drop the pairwise alpha-equivalent elements, then ask that what is left of
     l2 is covered by what is left of l1 *)
  let rec strip l1 l2 =
    match l2 with
        [] -> (l1, [])
      | b :: r2 ->
          let rec pull acc = function
              [] -> None
            | a :: rest ->
                if alpha_equiv a b then Some (List.rev_append acc rest)
                else pull (a :: acc) rest in
            (match pull [] l1 with
                 Some l1' -> strip l1' r2
               | None ->
                   let (l1'', r2'') = strip l1 r2 in
                     (l1'', b :: r2'')) in
  let (rest1, rest2) = strip l1 l2 in
    rest1 <> []
    && List.for_all (fun b -> List.exists (fun a -> ncpo p 1 aux a b) rest1) rest2

let gt p s t = ncpo p 1 [] s t

let compare p s t =
  if alpha_equiv s t then Equal
  else if gt p s t then Greater
  else if gt p t s then Less
  else Incomparable

let gt_heuristic p s t =
  match compare p s t with
      Greater -> true
    | Less | Equal -> false
    | Incomparable -> Term.compare s t > 0
