(* ========================================================================= *)
(* Term orderings for abstract term types                                    *)
(* ========================================================================= *)

(** Module Orderings implements partial term orderings over abstract term data types
    @author Arnaud
    @since 31-07-07*)

open Hol_type

exception NO_ORDER_INFO
exception ORDERINGS of string

type order = Greater | Equal | Unknown
type precedence 'a = ('a * order * 'a) list

let empty_order x y = Unknown

(*FIXME naive assoc list*)
let rec order_between prec s1 s2 =
  match prec with
      ((x1, o, x2) :: rest) ->
        if x1 = s1 && x2 = s2 then o
        else order_between rest s1 s2
    | [] -> Unknown

type status = Lex | Multi

let rec lex_lift_gte strict ord ls1 ls2 =
  match (ls1, ls2) with
      ([], []) -> not strict
    | ([x], [y]) ->
        (if strict then false else ord x y = Equal) ||
          ord x y = Greater
    | (x :: xs, y :: ys) ->
        (ord x y = Greater ||
            (ord x y = Equal && lex_lift_gte strict ord xs ys))
    | _ -> raise (ORDERINGS "Invalid arguments: lists must have same length")

(*FIXME naive*)
let ms_lift_gte strict ord ls1 ls2 =
  let sort_ord x y =
    if ord x y = Greater then 1
    else if ord x y = Equal then 0
    else -1 in
  let rec ms_lift_gte' ls1 ls2 =
    match (ls1, ls2) with
        ([], []) -> not strict
      | (_, []) -> true
      | ([], _) -> false
      | ([x], [y]) ->
          (if strict then false else ord x y = Equal) ||
          ord x y = Greater
      | (x :: xs, y :: ys) ->
          (ord x y = Greater ||
              (ord x y = Equal && ms_lift_gte' xs ys)) in
  let ls1' = List.rev (List.sort sort_ord ls1) in
  let ls2' = List.rev (List.sort sort_ord ls2)
  in ms_lift_gte' ls1' ls2'

type typeorder = hol_type -> int
type symbolorder = string -> int

module type TERM_TYPE =
sig
  type t
  type boundvars = t -> hol_type
  val is_symbol : t -> bool
  val is_var : t -> bool
  val is_const : t -> bool
  val is_abstr : t -> bool
  val is_appl : t -> bool
  val dest_symbol : t -> string
  val dest_abstr : t -> t * hol_type * t
  val dest_appl : t -> t * t
  val dest_flat_appl : t -> t * t list
  val type_of : boundvars -> t -> hol_type
  val adjoin : boundvars -> t -> hol_type -> boundvars
  val mk_symbol : string -> t
  val apply_and_normalise : t * t -> t
  val alpha_equiv : t -> t -> bool
  val free_vars : t -> string list
end

(*FIXME hack*)
let next_fresh = ref 0
let get_next_fresh_var () =
  next_fresh := !next_fresh + 1;
  string_of_int !next_fresh

(* FIXME currently only "None" and "Naive" are used. They are ordering
   based on embedding terms into nat. "Simple" would improve "Naive" by
   taking types into account. "CPO" would be better still, but is expensive
   to compute.
   Using "Simple" and "CPO" requires generalising the definitions related
   to term/literal/clause ordering in Leo2 -- currently these rely on an
   embedding of terms/literals/clauses into nat, but that's not
   sufficiently general.
*)
type ordering = None | Naive | Simple | CPO

let available_orderings = [None; Naive]

let ordering_of_string = function
  | "none" -> None
  | "naive" -> Naive
  | "simple" -> Simple
  | "cpo" -> CPO
  | s -> failwith ("Unrecognised ordering: " ^ s)

let ordering_to_string = function
  | None -> "none"
  | Naive -> "naive"
  | Simple -> "simple"
  | CPO -> "cpo"

module type TERM_ORDERING_FUNCTOR =
  functor (Termstruct : TERM_TYPE) ->
sig
  type term = Termstruct.t

  (** weighting functions **)
  val allTermsEqual : term -> int
  val constVars_typeConsts_offsetAbs_addApp : int -> int -> term -> int

  (** ordering functions **)
  (*emulates old behaviour in Leo2 at version 1.4.3 -- everything had the same weight*)
  val none : term -> term -> bool
  val simple : typeorder -> symbolorder -> (string -> hol_type) -> Termstruct.boundvars -> term -> term -> bool
  val cpo : term precedence -> Hol_type.hol_type precedence ->
    (term -> status) -> (string * Hol_type.hol_type) list ->
    term -> term -> bool
end

(*FIXME hack -- this is set in Interactive.init_problem, when problem's signature has been determined,
        and in Main.create_and_insert_new_free_var_with_simple_name and Main.create_and_insert_skolem_const
        (when the signature is updated)*)
let symbol_typings : (string * Hol_type.hol_type) list ref = ref []

module TermOrderingFunctor : TERM_ORDERING_FUNCTOR =
  functor (Termstruct : TERM_TYPE) ->
struct
  type term = Termstruct.t

  (*emulates constant weights used up to, and including, rev. 1545*)
  let allTermsEqual _ = 1

  (*emulates the (unused) term_weight which existed in module Term until r1545*)
  let rec eqSym_incAbs_addApp t =
    if Termstruct.is_symbol t then 1
    else if Termstruct.is_abstr t then
      let (_, _, t') = Termstruct.dest_abstr t
      in 1 + eqSym_incAbs_addApp t'
    else if Termstruct.is_appl t then
      let (t1, t2) = Termstruct.dest_appl t
      in eqSym_incAbs_addApp t1 + eqSym_incAbs_addApp t2
    else failwith "Could not process term"

  (*generalisation of eqSym_incAbs_addApp:
      variables assigned var_weight
      consts assigned symbolorder weight, or unk_const_weight if undefined
      abstractions are offset by a constant
      applications are additive*)
  let rec constVars_offsetAbs_addApp symbolorder var_weight unk_const_weight abs_offset t =
    if Termstruct.is_symbol t then
      if Termstruct.is_var t then var_weight
      else
        let s = Termstruct.dest_symbol t
        in try symbolorder s with NO_ORDER_INFO -> unk_const_weight
    else if Termstruct.is_abstr t then
      let (_, _, t') = Termstruct.dest_abstr t
      in abs_offset + constVars_offsetAbs_addApp symbolorder var_weight unk_const_weight abs_offset t'
    else if Termstruct.is_appl t then
      let (t1, t2) = Termstruct.dest_appl t
      in constVars_offsetAbs_addApp symbolorder var_weight unk_const_weight abs_offset t1 +
           constVars_offsetAbs_addApp symbolorder var_weight unk_const_weight abs_offset t2
    else failwith "Could not process term"

  (*Specialisation of constVars_offsetAbs_addApp where instead of symbolorder and
    unk_const_weight parameters we use the signature_precedence value*)
  let rec constVars_typeConsts_offsetAbs_addApp var_weight abs_offset t =
    let unk_const_weight = 1 (*should never be needed*) in
    (*compute a precedence favouring reduced type*)
    let rec arity_prec ty1 ty2 =
      match (ty1, ty2) with
          (Basetype s1, Basetype s2) -> String.compare s1 s2
        | (Funtype _, Basetype _) -> 1
        | (Basetype _, Funtype _) -> -1
        | (Funtype (ty1a, ty1b), Funtype (ty2a, ty2b)) ->
            (*FIXME explore other ways of comparing these two types*)
            let compare_arg = arity_prec ty1a ty2a
            in
              if compare_arg <> 0 then compare_arg
              else arity_prec ty1b ty2b in
    let cmp_typing ((_, ty1) : string * hol_type) (_, ty2) : int = arity_prec ty1 ty2 in
    let signature_precedence : symbolorder = fun s ->
      if List.mem s Signature.interpreted_constants then 10 (*FIXME interpreted symbols -- how to handle?*)
      else
        (* let symbol_typings = Signature.all_uninterpreted_symbols st.signature in *)
        let ordered_symbol_typings = List.sort cmp_typing !symbol_typings(*FIXME hack*) in
        let (found, idx) =
          List.fold_right
            (fun (s', _) ((found, idx) as result) ->
               if found then result
               else (s = s', idx + 1))
            ordered_symbol_typings
            (false, -1)
        in
          IFDEF DEBUG THEN
            assert found;
            if found then idx + 1 else unk_const_weight
          ELSE
            idx + 1
          END;
    in constVars_offsetAbs_addApp signature_precedence var_weight unk_const_weight abs_offset t

  (*Typed-based weighting of terms, which doesn't descend through terms
    (i.e. just looks at the surface term's type).
    Args:
     sigma types constants
     gamma types (free) variables*)
  let nonrec_typed_cumulAbs_addApp typeorder sigma gamma t =
    if Termstruct.is_var t then typeorder (gamma t)
    else if Termstruct.is_symbol t then
      typeorder (sigma (Termstruct.dest_symbol t))
    else if Termstruct.is_abstr t then
      let (x, x_ty, t') = Termstruct.dest_abstr t in
      let t'_ty = Termstruct.type_of (Termstruct.adjoin gamma x x_ty) t'
      in
        typeorder x_ty +
          typeorder t'_ty +
          typeorder (abstr_type x_ty t'_ty) (*i.e. weight of t's type*)
    else if Termstruct.is_appl t then
      let (t1, t2) = Termstruct.dest_appl t in
      let t1_ty = Termstruct.type_of gamma t1 in
      let t2_ty = Termstruct.type_of gamma t2
      in typeorder t1_ty + typeorder t2_ty
    else failwith "Could not process term"

  let none _ _ = false

  let simple typeorder symbolorder sigma gamma t1 t2 =
    let w1 = constVars_offsetAbs_addApp symbolorder 1 1 1 in
    let w2 = nonrec_typed_cumulAbs_addApp typeorder sigma gamma in
    let t1_w1 = w1 t1 in
    let t2_w1 = w1 t2
    in t1_w1 > t2_w1 || (t1_w1 = t2_w1 && w2 t1 > w2 t2)

  (*a weak type ordering, inferred from a type precedence.*)
  (*FIXME check required properties*)
  (*FIXME some inference for type_prec?*)
  let rec type_ord type_prec ty1 ty2 =
    if is_funtype ty1 then
      let (ty1a, ty1b) = Hol_type.dest_funtype ty1 in
        if ty1b = ty2 then Greater (*right arrow subterm property*)
        else
          if is_funtype ty2 then
            let (ty2a, ty2b) = dest_funtype ty2 in
              if type_ord type_prec ty1a ty2a = Greater then
                Greater
              else if type_ord type_prec ty1a ty2a = Equal then
                type_ord type_prec ty1b ty2b
              else
                Unknown
          else
            Unknown
    else if is_funtype ty2 then Unknown
    else type_prec ty1 ty2

  (*as described in "End of the quest" paper by Blanqui et al, CSL 2008
    stats is total function from constants to status
    vars is a set of variable symbols (and their types)
    prec is a precedence over constants
  *)
  let rec cpo_ty_gt prec type_qo stats vars (s_t, s_ty) (t_t, t_ty) =
    let ty_comparison = order_between type_qo s_ty t_ty
    in
      if cpo prec type_qo stats vars s_t t_t &&
        (ty_comparison = Greater || ty_comparison = Equal) then
          Greater
      else Unknown

  and cpo (prec : term precedence) (type_qo : Hol_type.hol_type precedence) stats vars (s : Termstruct.t) (t : Termstruct.t) =
    let bvars =
      List.fold_right
        (fun (s, ty) f x ->
           if x = Termstruct.mk_symbol s then ty else f x)
        vars
        (fun _ ->
           raise (ORDERINGS "Variable not in context")) in
    let pair_term_with_type x = (x, Termstruct.type_of bvars x) in
    let case_1_a () =
      Termstruct.is_var t &&
        List.mem_assoc (Termstruct.dest_symbol t) vars in
    let case_1_b f ss =
      Termstruct.is_appl t &&
        let (g, ts) = Termstruct.dest_flat_appl t
        in
          order_between prec f g = Equal &&
            cpo_s prec type_qo stats vars s ts &&
            (let ss' = List.map pair_term_with_type ss in
             let ts' = List.map pair_term_with_type ts
             in
               if stats f = Lex then
                 lex_lift_gte true (cpo_ty_gt prec type_qo stats [] (*FIXME vars?*)) ss' ts'
               else if stats f = Multi then
                  ms_lift_gte true (cpo_ty_gt prec type_qo stats [] (*FIXME vars?*)) ss' ts'
               else
                 raise (ORDERINGS "Unrecognised status")
            )
 in
    let case_1_c f =
      Termstruct.is_appl t &&
        let (g, ts) = Termstruct.dest_flat_appl t
        in
          (Termstruct.is_var g || order_between prec f g = Greater) &&
           cpo_s prec type_qo stats vars s ts in

    (*if free_z then z is free in the subsequent checks*)
    let t_is_abstr free_z =
      Termstruct.is_abstr t &&
        let (_, ty, _) = Termstruct.dest_abstr t in
        let z = "ZZ"(*FIXME const*) ^ get_next_fresh_var () in
        let w' = Termstruct.apply_and_normalise (t, Termstruct.mk_symbol z) in
        let vars' = if free_z then vars else (z, ty) :: vars
        in
          cpo prec type_qo stats vars' s w' in

    (*FIXME stronger than cpo, since also checks types*)
    let cpo_ty_gte empty_vars s' t' =
      Termstruct.alpha_equiv s' t' || (*FIXME use alpha equiv instead of structural equality*)
       (cpo_ty_gt prec type_qo stats (if empty_vars then [] else vars)
          (s', Termstruct.type_of bvars t')
          (t', Termstruct.type_of bvars t') = Greater) in

    let case_1_e ss = List.exists (fun s' -> cpo_ty_gte true s' t) ss in

    let case_2_b u v =
      Termstruct.is_appl t &&
        let (u', v') = Termstruct.dest_appl t
        in
          ms_lift_gte true (cpo_ty_gt prec type_qo stats [] (*FIXME vars?*))
            [pair_term_with_type u; pair_term_with_type v]
            [pair_term_with_type u'; pair_term_with_type v'] in

    let case_2_d u v = cpo_ty_gte false u t || cpo_ty_gte false v t in

    let cpo_gte s' t' =
      Termstruct.alpha_equiv s' t' ||
        cpo prec type_qo stats vars s' t' in

    (*beta case*)
    let case_2_e u v =
      let s' = Termstruct.apply_and_normalise (u, v)
      in Termstruct.is_abstr u && cpo_gte s' t in

    let case_3_b_and_c x_ty =
      Termstruct.is_abstr t &&
        let (_, y_ty, _) = Termstruct.dest_abstr t in
        let z =
          Termstruct.mk_symbol
            ("ZZ"(*FIXME const*) ^ get_next_fresh_var ()) in
        let t' = Termstruct.apply_and_normalise (t, z)
        in
          if order_between type_qo x_ty y_ty = Equal then
            let s' = Termstruct.apply_and_normalise (s, z)
            in
              cpo prec type_qo stats vars s' t'
          else
            cpo prec type_qo stats vars s t' in

    let case_3_d () =
      let z =
        Termstruct.mk_symbol
          ("ZZ"(*FIXME const*) ^ get_next_fresh_var ()) in
      let s' = Termstruct.apply_and_normalise (s, z)
      in
        cpo_ty_gte false s' t in

    (*eta case*)
    let case_3_e u =
      Termstruct.is_appl u &&
        let (v, x) = Termstruct.dest_appl t
        in
          Termstruct.is_var x &&
            (not (List.mem (Termstruct.dest_symbol x)
                    (Termstruct.free_vars v))) &&
            cpo_gte v t

    in
      (*start*)
      if Termstruct.is_appl s || Termstruct.is_symbol s then
        let (f, v) = Termstruct.dest_appl s
        in
          if not (Termstruct.is_var f) then (*case 1*)
            let (_, ss) = Termstruct.dest_flat_appl s (*if "s" is symbol then get (s, [])*)
            in
              assert (Termstruct.is_symbol f); (*since "s" should be in normal form*)
              case_1_a () ||
              case_1_b f ss ||
              case_1_c f ||
              t_is_abstr false ||
              case_1_e ss
          else (*case 2*)
            case_1_a () ||
            case_2_b f v ||
            t_is_abstr true ||
            case_2_d f v ||
            case_2_e f v
      else if Termstruct.is_abstr s then (*case 3*)
        let (_, x_ty, u) = Termstruct.dest_abstr s
        in
          case_1_a () ||
          case_3_b_and_c x_ty ||
          case_3_d () ||
          case_3_e u
      else raise (ORDERINGS "Check term")
  and cpo_s prec type_qo stats vars (s : Termstruct.t) (ts : Termstruct.t list) =
    match ts with
        [] -> true
      | (t :: ts) -> cpo prec type_qo stats vars s t &&
          cpo_s prec type_qo stats vars s ts
end

module ExplicitTerm : TERM_TYPE with type t = Term.term =
struct
  type t = Term.term
  type boundvars = Term.term -> hol_type

  let is_symbol = Term.is_symbol
  let is_var = Term.is_variable
  let is_const = function t -> Term.is_symbol t && (not (Term.is_variable t))
  let is_abstr = Term.is_abstr
  let is_appl = Term.is_appl

  let dest_symbol = Term.get_symbol
  let dest_abstr = function
      Term.Abstr(t, ty, t') -> (t, ty, t')
    | _ -> failwith "not an abstraction"
  let dest_appl = function
      Term.Appl(t1, t2) -> (t1, t2)
    | _ -> failwith "not an application"
  let rec dest_flat_appl' t acc =
    match t with
        Term.Appl(t1, t2) -> dest_flat_appl' t1 (t2 :: acc)
      | _ -> (t, acc)
  (*unlike "dest_flat", "dest_flat_appl" doesn't fail if not given an application*)
  let dest_flat_appl t = dest_flat_appl' t []

  let type_of gamma = Term.type_of (fun x -> gamma (Term.Symbol x))
  let adjoin gamma v t = fun x -> if x = v then t else gamma x

  let mk_symbol s = Term.Symbol s
  let apply_and_normalise (t1, t2) =
    Term.beta_normalize (Term.Appl(t1, t2))

  let alpha_equiv = Term.alpha_equiv
  let free_vars = Term.free_vars
end

(*FIXME currently disabled, since not being used elsewhere
module TermsetTerm : TERM_TYPE with type t = Termset.id =
struct
  type t = Termset.id
  type boundvars = Termset.id -> hol_type
  let ts = ref (Termset.new_termset ())

  let is_symbol id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Symbol_node _ | Termset.Bound_node _ -> true
      | _ -> false
  let is_var id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Bound_node _ -> true
      | _ -> false
  let is_const id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Symbol_node _ -> true
      | _ -> false
  let is_abstr id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Abstr_node _ -> true
      | _ -> false
  let is_appl id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Appl_node _ -> true
      | _ -> false

  let dest_symbol id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Symbol_node s -> s
      | _ -> failwith "not a symbol"
  let dest_abstr id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Abstr_node(ty, id') -> (0, ty, id') (* hack *)
      | _ -> failwith "not an abstraction"
  let dest_appl id =
    match (Termset.get_node !ts id).Termset.structure with
        Termset.Appl_node(id1, id2) -> (id1, id2) (* hack *)
      | _ -> failwith "not an application"
  let dest_flat_appl' id acc = (*if dest_appl is a hack then this must be too*)
    match id with
        Termset.Appl_node(id1, id2) -> dest_flat_appl' id1 (id2 :: acc)
      | _ -> (id, acc)
  (*unlike "dest_flat", "dest_flat_appl" doesn't fail if not given an application*)
  let dest_flat_appl id = dest_flat_appl' id []

  let type_of _ = Termset.node_type !ts
  let adjoin gamma _ _ = gamma (* dummy *)
end
  *)

(*FIXME hack, need to reorganise module dependencies*)
module Ords = TermOrderingFunctor(ExplicitTerm)
let weighting_hook : (Ords.term -> int) ref = ref (fun _ -> failwith "Undefined term weighting")
let set_ord ordering =
  match (*State.get_flag_termweight State.state_initialize*) ordering with (*FIXME hack, using lax state management in Leo*)
    | None -> weighting_hook := Ords.allTermsEqual
    | Naive -> weighting_hook := Ords.constVars_typeConsts_offsetAbs_addApp 3 1
    | _ -> raise (ORDERINGS "Unsupported ordering")

(*FIXME above approach is very limited. Should generalise to something of the following form:
let ordering_hook : (Ords.term -> Ords.term -> bool) ref = ref (fun _ _ -> failwith "Undefined term ordering")
let set_ord ordering =
  match (*State.get_flag_termorder State.state_initialize*) ordering with (*FIXME hack, using lax state management in Leo*)
    | None
    | Simple
    | CPO -> ordering_hook := (fun _ _ -> false)
*)
