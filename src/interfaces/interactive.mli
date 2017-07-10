(* ========================================================================= *)
(* Interactive Command Line Interpreter                                      *)
(* ========================================================================= *)

(** Module Interactive implements LEO's command line interpreter
   @author Chris
   @since 27-11-06*)

val fo_translations : string list

(** {6 Invoking the Command Line Interpreter } *)

val kill_children : unit -> unit

val initialize : unit -> State.state

val comint : unit -> unit

val resume : unit -> unit

val leo_state : State.state ref

val get_timeout : int

val set_timeout : int -> unit

val set_original_timeout : int -> unit

val start_timeout : unit -> unit

val end_timeout : unit -> unit

val handle_timeout : unit -> unit

val analyze_problem : State.state -> (int * int * bool)

exception Timeout
