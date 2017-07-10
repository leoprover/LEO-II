(* ========================================================================= *)
(* Clauses                                                                   *)
(* ========================================================================= *)

(** Module Clause implements clauses and simple operations on clauses 
   @author Chris 
   @since 27-11-06*)

open Term
open Termsystem
open Literal
open Clause
open Clauseset
open State
open Main

(** {6 New Exception for Calculus Rule Failure} *)

(** Exception for Resolution Failures *)

exception Calculus_failure of string

exception Literal_not_found

(** {6 The Calculus Rules} *)

(** Exhaustive Unfolding of Defined Symbols *)

(* val unfold_def_info : state  -> (cl_number * ((cl_number * int * string * string) * role xterm * role xterm) list) list *)

val fold_node_exhaustively : state  -> int -> (role list) * (cl_clause list) * (cl_clause list)

val unfold_defs_exhaustively : state  -> (role list) * (cl_clause list) * (cl_clause list)

(** Exhaustive Clause Normalisation *)

val cnf_normalize_step : cl_clause -> state -> cl_clause list

val standard_extcnf_term: term -> state -> term

val standard_extcnf : cl_clause -> state -> cl_clause list

(* val cnf_normalize_clauseset : Set_of_clauses.t -> state -> cl_clause list *)

(* val cnf_exhaustively_normalize : cl_clause -> state -> cl_clause list *)

(* val cnf_exhaustively_normalize_clauselist : cl_clause list -> state -> cl_clause list *)

(* val cnf_exhaustively_normalize_clauseset : Set_of_clauses.t -> state -> cl_clause list *)

(** Useful Functions *)

val classify_role : state -> role -> string

val is_uni_lit : role lit_literal -> bool

val has_uni_lit : cl_clause -> bool

val rename_free_variables : cl_clause -> state -> cl_clause

(** The Resolution Rule *) 

val resolve : cl_clause -> cl_clause -> state -> cl_clause list

(** The Restricted Factorization Rule (only two literals, but extensional) *) 

val factorize_restricted : cl_clause -> state -> cl_clause list

(** The Decomposition Rule *)

val decompose : cl_clause -> state -> cl_clause list

 (* val decompose_exhaustively : cl_clause -> state -> cl_clause list *)

(** The Simplification Rule *)

val simplify : cl_clause -> state -> cl_clause list

val simplify_global : state -> (cl_clause * (cl_clause list)) list

(** Clause factorization *)

val clause_factorization : state -> (cl_clause * (cl_clause list)) list


(** The Trivial Rule *)

val trivial : cl_clause -> state -> cl_clause list


(** The Substitute or Clash Rule *)

val subst_or_clash : cl_clause -> state -> cl_clause list

(* val substitute_or_clash_clause_exhaustive : cl_clause -> state -> cl_clause list *)

(** The Boolean Extensionality Rule *)

val boolean_ext : cl_clause -> state -> cl_clause list

val boolean_ext_pos : cl_clause -> state -> cl_clause list

val boolean_ext_pos_main_loop : cl_clause -> state -> cl_clause list

(** The Functional Extensionality Rule *)

val functional_ext : cl_clause -> state -> cl_clause list

val functional_ext_pos : cl_clause -> state -> cl_clause list

(* val functional_ext_exhaustively : cl_clause -> state -> cl_clause list *)

(* val functional_ext_pos_exhaustively : cl_clause -> state -> cl_clause list *)

(** The Functional Unification Rule *)

val func_uni : cl_clause -> state -> cl_clause list

(** The Flex-Rigid Rule *)

val flex_rigid : cl_clause -> state -> cl_clause list

(** The Prim-Subst Rule *)

val prim_subst : cl_clause -> state -> cl_clause list

(** The (Extensional) Pre-Unification Rule *)

val pre_unify : cl_clause -> state -> cl_clause list

(** The Subsumption Rules *)

val triv_subsumes : cl_clause -> cl_clause -> bool

val fo_match_subsumes : cl_clause -> cl_clause -> state -> bool

(** Simple Relevance Filtering *)

val filter_axioms_wrt_conjecture : state -> cl_clause list -> cl_clause list -> int -> cl_clause list

(** New Primsubst Rule *)

val primsubst_new : cl_clause list -> state -> cl_clause list

(** Replace Leibniz Lits Rule *)

val replace_leibniz_lits : cl_clause -> state -> cl_clause list

val replace_andrews_lits : cl_clause -> state -> cl_clause list


(** Apply Choice Rule (exhaustive) *)

val detect_choice : cl_clause -> state -> cl_clause list

val apply_choice : cl_clause -> state -> cl_clause list
