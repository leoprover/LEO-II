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
type 'a precedence = ('a * order * 'a) list

type status = Lex | Multi

(** the type of type orderings *)
type typeorder = hol_type -> int

(** the type of symbol weights *)
type symbolorder = string -> int

(** signature of abstract term data structure, input signature for functor [TermOrderingFunctor] *)
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

(** A setting selects two things: a term weight, which clause selection uses
    and which must be total and cheap, and an orientation order, which is
    decided one pair at a time and may leave a pair undecided.  They are
    separate because the orientation order is not known to be transitive and
    therefore cannot order a set of clauses.

    - [None] gives every term the same weight and orients nothing, which is
      what LEO-II did up to 1.7.
    - [Naive] weighs by a precedence read off the signature.
    - [Weight] counts symbols.  Over the ontological-argument problems of
      Benzmüller and Scott it proves as many as [None] does and no more, so it
      is offered rather than imposed: [None] remains the default.
    - [Ncpo] counts symbols and adds the computability path order of
      {!Ncpo} as the orientation order. *)
type ordering = None | Naive | Weight | Ncpo | Simple | CPO

val available_orderings : ordering list
val ordering_of_string : string -> ordering
val ordering_to_string : ordering -> string

val symbol_typings : (string * Hol_type.hol_type) list ref

(** functor returning a structure implementing orderings over term *)
module TermOrderingFunctor :
  functor (Termstruct : TERM_TYPE) ->
    sig
      type term = Termstruct.t

      (** weighting functions **)
      val allTermsEqual : term -> int
      val symbol_count : int -> int -> term -> int
      val constVars_typeConsts_offsetAbs_addApp : int -> int -> term -> int

      (** ordering functions **)
      val none : term -> term -> bool
      val simple : typeorder -> symbolorder -> (string -> hol_type) -> Termstruct.boundvars -> term -> term -> bool
      val cpo : term precedence -> Hol_type.hol_type precedence ->
        (term -> status) -> (string * Hol_type.hol_type) list ->
        term -> term -> bool
    end

(** these should probably be moved to modules Term and Termset, respectively *)
module ExplicitTerm : TERM_TYPE with type t = Term.term
(* module TermsetTerm : TERM_TYPE with type t = Termset.id *)

val weighting_hook : (Term.term -> int) ref
(** The literal weight.  The calculus reads it: a clause's literals are sorted
    by it and the number carrying the maximum bounds factorisation, so changing
    it changes which inferences are performed. *)

val selection_weight_hook : (Term.term -> int) ref
(** The term weight behind the clause size that given-clause selection uses.
    Nothing in the calculus reads it, so it is free to be informative. *)

val term_order_hook : (Term.term -> Term.term -> bool) ref
(** The orientation order, asked about one pair at a time.  False in both
    directions means the pair is not oriented and the caller must do nothing.
    Never hand this to a sorting function: the order behind it is not known to
    be transitive. *)
val set_ord : ordering -> unit



