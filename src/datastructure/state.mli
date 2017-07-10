

type schedule =
  {duration : float;
   strategy : string list;
  }

val current_schedule : schedule ref
val child_time : float ref
val sys_time_offset : float ref
val problem_cumulative_time : float ref
val problem_overshot : float ref
val schedule_start : float ref

exception STRATEGY_TERMINATED

val time_remaining_of_schedule : unit -> float

val atp_subslices : int

val check_timeout : unit -> unit

type operating_mode =
    Unsatisfiable_vs_Satisfiable
  | Theorem_vs_CounterSatisfiable

(*Leo-II's configuration record*)
type configuration = {
  mutable foatp : string;
  mutable dir : string;
  mutable interactive : bool;
  mutable time_slices : int;
  mutable global_timeout : int;
  schedules : schedule Queue.t;
  mutable debug : int;
  mutable problemfiles : string list;
  mutable operating_mode : operating_mode;
  (*if None then use the strategy schedule's, otherwise force this timeout value*)
  mutable atp_timeout_forced : int option;
  mutable analyze : bool;
}

(*Leo-II's default initial config*)
val global_conf : configuration

type szs_status =
    CounterSatisfiable | Error | Force | GaveUp | ResourceOut
  | Satisfiable | Tautology | Theorem | Timeout| Unknown | Unsatisfiable | User

val szs_status_string : szs_status -> string

val current_problem_file : string ref

(** Logic being processed by Leo-II **)

val input_logic : string list ref

val get_input_logic : unit -> string list

val set_input_logic : string -> unit

val is_an_input_logic : string -> bool

val reset_input_logic : unit -> unit


(*Type of LEO-II flags*)
type flags = {
    mutable verbose : bool;
    mutable max_clause_count : int;
    mutable max_loop_count : int;
    mutable max_uni_depth : int;
    mutable write_protocol_files : bool;
    mutable write_fo_like_clauses : bool;
    mutable pretty_print_only : bool;
    mutable fo_translation : string;
    mutable atp_calls_frequency : int;
    mutable atp_prover : string;
    mutable atp_timeout : int;
    mutable proof_output : int;
    mutable protocol_output : bool;
    mutable prim_subst : int;
    mutable unfold_defs_early : bool;
    mutable relevance_filter : int;
    mutable replace_leibnizEQ : bool;
    mutable replace_andrewsEQ : bool;
    mutable use_choice : bool;
    mutable use_extuni : bool;
    mutable ordering : Orderings.ordering;
    mutable max_local_time : int;
    mutable sos : bool;
    mutable use_extcnf_combined : bool;
    mutable expand_extuni : bool;
  }

(*LEO's main search state*)
type state = {
    mutable origproblem : (string, string* Term.term) Hashtbl.t;
    mutable origproblem_filename : string;
    mutable origproblem_definitions : string;
    mutable origproblem_all_def_names : string;
    mutable signature : Signature.signature;
    mutable index : Clause.role Termset.termindex;
    mutable active : Clauseset.Set_of_clauses.t;
    mutable passive : Clauseset.Set_of_clauses.t;
    mutable active_debug : Clause.cl_clause list;
    mutable passive_debug : Clause.cl_clause list;
    mutable primsubst_waitlist : Clauseset.Set_of_clauses.t;
    mutable problem_axioms : Clause.cl_clause list;
    mutable problem_stack : Clause.cl_clause list;
    mutable free_var_count : int;
    mutable skolem_const_count : int;
    mutable clause_count : int;
    mutable loop_count : int;
    mutable clause_weight_func : Clause.cl_clause -> int;
    mutable empty_clauses : Clause.cl_clause list;
    mutable fo_clauses : (string * string) list;
    mutable fo_clauses_new : (string * Af.af) list;
    mutable foatp_calls : int;
    mutable choice_functions : Term.term list;
    mutable flags : flags;
  }


val get_current_success_status : unit -> szs_status
val set_current_success_status : state option -> szs_status -> unit

exception Termination of state option

val state_initialize : state

val state_reset : state -> unit

val state_reset_only_essentials : state -> unit

val set_origproblem : state -> (string, string * Term.term) Hashtbl.t -> unit

val set_origproblem_filename : state -> string -> unit

val set_origproblem_definitions : state -> string -> unit

val set_origproblem_all_def_names : state -> string -> unit

val set_signature : state -> Signature.signature -> unit

val set_active : state -> Clauseset.Set_of_clauses.t -> unit

val add_to_active : state -> Clause.cl_clause -> unit

val remove_from_active : state -> Clause.cl_clause -> unit

val set_passive : state -> Clauseset.Set_of_clauses.t -> unit

val set_primsubst_waitlist : state -> Clauseset.Set_of_clauses.t -> unit

val add_to_passive : state -> Clause.cl_clause -> unit

val add_to_primsubst_waitlist : state -> Clause.cl_clause -> unit

val remove_from_passive : state -> Clause.cl_clause -> unit

val remove_from_primsubst_waitlist : state -> Clause.cl_clause -> unit

val set_problem_axioms : state -> Clause.cl_clause list -> unit

val set_problem_stack : state -> Clause.cl_clause list -> unit

val set_choice_functions : state -> Term.term list -> Term.term list

val show_list : string list -> string

val add_choice_functions : state -> Term.term list -> Term.term list

val set_index : state -> Term.term list -> unit

val add_to_index : state -> Term.term -> unit

val set_free_var_count : state -> int -> int

val inc_free_var_count : state -> int

val set_skolem_const_count : state -> int -> int

val inc_skolem_const_count : state -> int

val set_clause_count : state -> int -> int

val inc_clause_count : state -> int

val inc_loop_count : state -> int

val set_loop_count : state -> int -> int

val set_clause_weight_func : state -> (Clause.cl_clause -> int) -> (Clause.cl_clause -> int)

val set_empty_clauses : state -> Clause.cl_clause list -> Clause.cl_clause list

val set_fo_clauses : state -> (string * string) list -> unit

val set_flag_verbose : state -> bool -> bool

val set_flag_sos : state -> bool -> bool

val set_flag_max_clause_count : state -> int -> int

val set_flag_max_loop_count : state -> int -> int

val set_flag_max_uni_depth : state -> int -> int

val set_flag_write_protocol_files : state -> bool -> bool

val set_flag_write_fo_like_clauses : state -> bool -> bool

val set_flag_pretty_print_only : state -> bool -> bool

val set_flag_fo_translation : state -> string -> string

val set_flag_atp_calls_frequency : state -> int -> int

val set_flag_atp_prover : state -> string -> string

val set_flag_atp_timeout : state -> int -> int

val set_flag_proof_output : state -> int -> int

val set_flag_protocol_output : state -> bool -> bool

val set_flag_prim_subst : state -> int -> int

val set_flag_unfold_defs_early : state -> bool -> bool

val set_flag_relevance_filter : state -> int -> int

val set_flag_replace_leibnizEQ : state -> bool -> bool

val set_flag_replace_andrewsEQ : state -> bool -> bool

val set_flag_use_choice : state -> bool -> bool

val set_flag_use_extuni : state -> bool -> bool

val set_flag_use_extcnf_combined : state -> bool -> bool

val set_flag_expand_extuni : state -> bool -> bool

val set_flag_max_local_time : state -> int -> int

val set_flag_termorder : state -> Orderings.ordering -> Orderings.ordering

val get_flag_termorder : state -> Orderings.ordering


(** Info provided to the outside **)

(*Provide summary of prover state. This is used to
  inform the user on exit, and could be used in
  intermediate stages*)
val summary_stats_string : state -> string

val szs_result : state option -> string

val szs_exitcode : unit -> int

IFDEF GIVENCLAUSEGRAPH THEN
val lastloop_no : int ref
val lastloop_ran : bool ref
val print_actpas_sets : Clause.cl_clause -> Clause.cl_clause -> Clauseset.Set_of_clauses.t -> state -> unit
ENDIF
