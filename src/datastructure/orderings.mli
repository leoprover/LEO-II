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
type precedence 'a = ('a * order * 'a) list

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

type ordering = None | Naive | Simple | CPO

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

(*val ordering_hook : (Term.term -> Term.term -> bool) ref*)
val weighting_hook : (Term.term -> int) ref
val set_ord : ordering -> unit



