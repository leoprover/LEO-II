(* ========================================================================= *)
(* LEO's Global Search State                                                 *)
(* ========================================================================= *)

(** Module Main implements LEO's main search state  
   @author Chris 
   @since 27-11-06*)


open Term
open Termset
open Termsystem
open Signature
open Literal
open Clause
open Clauseset
open Hol_type
open State

exception EMPTYCLAUSE_DERIVED
exception MAX_CLAUSES
exception MAX_LOOPS
exception ACTIVE_EMPTY


(** {6 Type Declarations} *)

type protocol = int * (string * (int * string) list * string) * string

(** {6 Finding and Removing Clauses } *)

val find_clause_by_number : state -> int -> cl_clause

val find_and_remove_clause_by_number : state -> int -> cl_clause

val find_and_remove_clause_by_number_in_active : state -> int -> cl_clause

val find_and_remove_clause_by_number_in_passive : state -> int -> cl_clause

(** {6 Further Important Operations} *)

val mk_clause : role lit_literal list -> cl_number -> term list -> cl_info -> cl_origin -> state -> cl_clause

val index_clause_with_role : cl_clause -> state -> unit

val index_clauselist_with_role : cl_clause list -> state -> unit

val index_clear_all_roles : state -> unit

val mk_clause_and_index_with_role : role lit_literal list -> cl_number -> term list -> cl_info -> cl_origin -> state -> cl_clause

val choose_and_remove_lightest_from_active : state -> cl_clause

val cl_clause_to_fotptp_cnf : cl_clause -> state -> (string * string) list


(** {6 Construction of terms with new symbols (and registration in state)} *)

val create_and_insert_new_free_var : term -> hol_type -> state -> term

val create_and_insert_new_free_var_with_simple_name : hol_type -> state -> term

val create_and_insert_skolem_const : term -> hol_type -> state -> term


(** {6 Expansion of definitions} *)

val unfold_logical_defs : term -> state -> term

val unfold_nonlogical_defs : term -> state -> term



(** {6 Pretty Printing} *)

val state_to_string : state -> string

val state_to_post : state -> string

val origproblem_to_post : state -> string

val origproblem_to_string : state -> string

val origproblem_to_hotptp : state -> string

(** {6 Verbose Output or Not} *)

val output : state -> (unit -> string) -> unit

val output_debug : string -> unit

(** {6 Proof Protocol} *)

val protocol_init : unit -> unit

val add_to_protocol : protocol -> state-> unit

val print_protocol : unit -> unit

val print_protocol_tstp : state -> unit

val derivation : (int * string) option -> state -> string

val derivation_tstp : (int * string) option -> state -> string

val print_derivation : (int * string) option -> state -> unit

val print_derivation_tstp : (int * string) option -> state -> unit


(** {6 FO Clauses in FOTPTP CNF representation} *)

val fo_clauses_init : state -> unit

val add_fo_clauses : cl_clause list -> state -> unit

val get_fo_clauses : state -> string

val get_fo_clauses_numbers : state -> int list


(** {6 Check for local max time (raise timeout)} *)

val check_local_max_time : state -> bool


(** {6 Nonlogical symbols in a clause} *)

val uninterpreted_and_nonlogical_symbols_in_clause : cl_clause -> state -> (role xterm) list


(** {6 Expand definitions in clause} *)

val expand_nonlogical_defs: cl_clause -> state -> cl_clause list

val expand_logical_defs: cl_clause -> state -> cl_clause list


(** {6 Others} *)

val ground_poly_syms : term -> state -> term
