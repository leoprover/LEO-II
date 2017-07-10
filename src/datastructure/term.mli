(* ========================================================================= *)
(* User readable terms                                                       *)
(* ========================================================================= *)

(** Module Term implements HOL terms.
    @author Frank, Chris
    @since 07-06-06*)

open Hol_type

(*FIXME move this elsewhere*)
exception PARSER

(** The user-readable terms have a simple structure which should not
    be hidden in an ADT.
    The insertion into the termset is easier to implement if the term
    structure is public. *) 
type term =
  Symbol of string |
  Appl of term * term |
  Abstr of term * hol_type * term

val alpha_equiv : term -> term -> bool

val compare : term -> term -> int

(** {6 Operations on Terms} *)

val is_symbol : term -> bool
(** Checks whether the given term is a symbol. *)

val is_variable : term -> bool
(** Checks whether the given term is a variable.
    Note: we adhere to the  convention that variable names always start with
    with an uppercase symbol. *)


val get_symbol : term -> string
(** Returns the string name of the symbol represented by the given term. Raises
    [Failure "not a symbol"] if the term is not a symbol. *)

val is_appl : term -> bool
(** Checks whether the given term is an application. *)

val is_abstr : term -> bool
(** Checks whether the given term is an abstraction. *)

val free_vars : term -> string list
(** Returns the list of free variables of a term. *)

val term_symbols : term -> string list
(** Returns the list of symbols (uis) of a term. *)

val get_head_symbol : term -> term
(** Returns the head symbol of a term. *)

val type_of : (string -> hol_type) -> term -> hol_type

val types_of_all_arg_terms_up_to_term : term -> term -> (string -> hol_type) -> (bool * hol_type list)

val beta_normalize : term -> term
(** Returns the beta-normal form of the given term. *)

val subst_symbols : (string * term) list -> term -> term
(** Returns the beta-normal form of the given term. *)

val multi_abstr : (string * hol_type) list -> term -> term
(** given [(x1,ty1),...,(xn,tyn)] and t, returns Abstr(x1,ty1,Abstr(x2,ty2,...t...)). *)

val de_multi_abstr : term -> (string * hol_type) list * term
(** inverse of multi_abstr, i.e.
    given Abstr(x1,ty1,Abstr(x2,ty2,...t...)), returns ([(x1,ty1),...,(xn,tyn)], t). *)

val multi_quantified : term -> (string * hol_type) list -> term -> term
(** given Q, [(x1,ty1),...,(xn,tyn)] and t, returns Appl(Q,Abstr(x1,ty1,Appl(Q,Abstr(x2,ty2,...t...))))
    so it essentially turns [forall [(x1,ty1),...,(xn,tyn)] t] into forall(lambda x1:ty1. forall(lambda x2:ty2. ...t...)). *)

val de_multi_quantified : term -> term * (string * hol_type) list * term
(** inverse of multi_abstr, i.e.
		given Appl(Q,Abstr(x1,ty1,Appl(Q,Abstr(x2,ty2,...t...)))), returns
		(Q, [(x1,ty1),...,(xn,tyn)], t). *)

val smaller_head : term -> term -> bool

(** {6 Pretty Printing} *)

val to_string : term -> string
(** Returns a string representation of the given term. *)

val hotptpsymb_critical : string -> string
(** Mapping from strings to their HOTPTP presentation. This is the critical version which fails, if there is no special symbol *) 

val to_hotptp : term -> string
(** Returns a string representation of the given term, according to the HOTPTP syntax. *)

val to_compressed : term -> string

(*
val to_fotptp_cnf : signature -> term -> string
(** Returns a string representation of the given term, according to the FOTPTP CNF syntax. *)
*)

val to_post : term -> string
(** Returns a string representation of the given term, according to the POST syntax. *)

val termlist_to_string : term list -> string
(** Returns a string representation of the given termlist. *)
