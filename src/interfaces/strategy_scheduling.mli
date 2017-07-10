
exception STRATEGY of string

val execute_commands : string list -> bool

val compute_strategies : State.configuration -> string -> string list list
