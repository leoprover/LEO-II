(* ========================================================================= *)
(* Clauses                                                                   *)
(* ========================================================================= *)

(** Module Clausesets implements clausesets as ordered sets
   @author Chris
   @since 27-11-06*)

(** Set_of_clauses are realized as ordered sets. *)

module Set_of_clauses :
    sig
      type elt = Clause.cl_clause
      type t
      val empty : t
      val is_empty : t -> bool
      val mem : elt -> t -> bool
      val add : elt -> t -> t
      val singleton : elt -> t
      val remove : elt -> t -> t
      val union : t -> t -> t
      val inter : t -> t -> t
      val diff : t -> t -> t
      val compare : t -> t -> int
      val equal : t -> t -> bool
      val subset : t -> t -> bool
      val iter : (elt -> unit) -> t -> unit
      val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
      val for_all : (elt -> bool) -> t -> bool
      val exists : (elt -> bool) -> t -> bool
      val filter : (elt -> bool) -> t -> t
      val partition : (elt -> bool) -> t -> t * t
      val cardinal : t -> int
      val elements : t -> elt list
      val min_elt : t -> elt
      val max_elt : t -> elt
      val choose : t -> elt
      val split : elt -> t -> t * bool * t
    end

(** {6 Additional functions (not provided by the ordered sets functor)} *)

val cl_clauseset_to_string :  Set_of_clauses.t -> string

val list_to_set : Clause.cl_clause list -> Set_of_clauses.t

val ratio_strategy : Clause.cl_clause -> Clause.cl_clause -> int
