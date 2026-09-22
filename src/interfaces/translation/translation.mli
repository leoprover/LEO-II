
val tr_add_fo_clauses : Clause.cl_clause list -> State.state -> unit

(*the term a lambda-lifted symbol stands for, for reporting answers*)
val lifted_term_of : string -> string option
val reset_prev_fo_clauses_cache : unit -> unit
val next_atp_call_is_redundant : bool ref

val exc_printers : exn -> string option
