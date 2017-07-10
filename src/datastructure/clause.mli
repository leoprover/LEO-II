(* ========================================================================= *)
(* Clauses                                                                   *)
(* ========================================================================= *)

(** Module Clause implements clauses and simple operations on clauses 
   @author Chris 
   @since 27-11-06*)

open Term
open Literal
open Signature

(** {6 Type Declarations} *)

(** The type for clause numbers. *)

type cl_number = int

(** Type of Roles for Indexing *)
(* roles are tuples of information on the 
   - clause number
   - literal position 
   - whether literal is positive ("pos") or negative ("neg")
   - whether literal is maximal ("max") or not ("nmax")
*)

type role =  cl_number * int * string * string

val role_to_string : role -> string

(** The type for literal lists (arrays) in clauses. *)

type cl_literals = role lit_literal array

(** The type for clause weights. *)

type cl_weight = int

(** The type for clause infos -- preliminary. *)

type cl_info = string * (int * string) list * string

val cl_info_to_string : cl_info -> string


(** The type for the number of maximal literals in a clause *)

type cl_max_lit_num = int

(** The type for the origing of a clause *)

type cl_origin = 
    AXIOM 
  | CONJECTURE
  | DERIVED

val cl_origin_to_string : cl_origin -> string

(** The type for clauses; internals are hidden *)

type cl_clause = {
    cl_number : cl_number;
    cl_litarray : cl_literals;
    cl_max_lit_num: cl_max_lit_num;
    cl_weight : cl_weight;
    cl_free_vars : term list;  
    cl_info : cl_info;
    cl_origin : cl_origin
   }

(** {6 Access Functions} *)

val cl_number : cl_clause ->  cl_number

val cl_litarray : cl_clause -> cl_literals

val cl_weight : cl_clause -> cl_weight

val cl_free_vars : cl_clause -> term list

val cl_info : cl_clause -> cl_info

val cl_max_lit_num : cl_clause -> cl_max_lit_num

val cl_origin : cl_clause -> cl_origin

(** {6 Clause Creation and Manipulation} *)

(** Create a new clause rom a given literal list *)

val cl_mk_clause : role lit_literal list -> cl_number -> term list -> cl_info -> cl_origin -> cl_clause

(* val set_clause_weight : cl_clause -> int -> unit *)

(** Different representations of a clause *)

val cl_clause_to_string : cl_clause -> string

val cl_clause_to_protocol : cl_clause -> string

val cl_axiom_clause_to_thf : cl_clause -> string

val cl_negated_conjecture_clause_to_thf : cl_clause -> string

val cl_litarray_to_string : cl_literals -> string

val cl_clause_to_post : cl_clause -> string

(** String representation of a clauselist *)

val cl_clauselist_to_string : cl_clause list -> string

val cl_clauselist_to_protocol : cl_clause list -> string

(** Clause comparison (used in Clauseset for ordering purposes) *)

val cl_compare : cl_clause -> cl_clause -> int


