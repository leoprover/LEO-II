(* ========================================================================= *)
(* Automation                                                                *)
(* ========================================================================= *)

(** Module Automation implements the main reasoning loop of LEO-II
    -- Strongly Preliminary Version --
    @author Chris
    @since 07-03-07*)

open Term
open Literal
open Clause
open Clauseset
open State
open Main

(** {6 Lifting, composition and exhaustive application of rules} *)

val raise_to_list : (cl_clause -> state -> cl_clause list) -> (cl_clause list -> state -> cl_clause list)

val compose : (cl_clause list -> state -> cl_clause list) list -> (cl_clause list -> state -> cl_clause list)

val combine : (cl_clause -> state -> cl_clause list) -> (cl_clause -> state -> cl_clause list) -> (cl_clause -> state -> cl_clause list)

val exhaustive : (cl_clause list -> state -> cl_clause list) -> (cl_clause list -> state -> cl_clause list)

(** {6 Extensional Higher-Order Pre-Unification} *)

val unify_pre_ext : cl_clause -> state -> cl_clause list

val unify_pre_ext_old : cl_clause -> state -> cl_clause list

(** {6 Call FO ATP} *)

val supported_atps : string list

val atp_versions : unit -> unit

val get_atp_times : unit -> (float * string) list

val call_fo_atp : state -> string -> unit

val call_fo_atp_early : state -> string -> unit

val atp_config_file : string ref

val atp_configured : bool ref

val atp_cmds : (string * string) list ref

(** {6 Complete Pre-Processing of the Problem State} *)

val pre_process : state -> cl_clause list

(* val pre_process_1_with_stack : state -> state *)

(*
(** {6 Dialogs that are used by modules automation and interactive} *)

val proof_found : state -> bool

val proof_found_subdialog : state -> unit

val write_fo_like_clauses_subdialog : state -> unit
*)


(** {6 LEO-II's Main Reasoning Loop} *)

val loop : state -> unit

(* val prove : state -> unit *)

(* val prove_with_fo_atp : state -> string -> bool *)
