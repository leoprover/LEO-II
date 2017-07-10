(* ========================================================================= *)
(* Literals                                                                  *)
(* ========================================================================= *)

(** Module Literal implements literals and operations on literals. 
    -- Strongly Preliminary Version; not linked to real terms yet --
    @author Chris
    @since 27-11-06*)

open Termset
open Termsystem

(** {6 Type Declarations} *)

(** The type for literal weights - preliminary*)

type lit_weight = int


(** Test whether two literal terms are equals *) 

val lit_term_equal : 'a xterm -> 'a xterm -> bool 

(** The type for literal infos - preliminary*)

type lit_info = string 

(** The type for literal polarities *)

type lit_polarity = bool 

(** The type for literals. Convention: all literals are equations left == right, i.e., they have a left term and a right term; furthermore, literals have a weight and an info --- preliminary*)

type 'a lit_literal = {
  lit_term : 'a xterm;
  lit_polarity : lit_polarity;
  lit_weight : lit_weight;
  lit_info : lit_info;
  } 

(** {6 Access Functions} *)


val lit_term : 'a lit_literal -> 'a xterm

val lit_polarity : 'a lit_literal -> lit_polarity

val lit_weight : 'a lit_literal -> lit_weight

val lit_info : 'a lit_literal -> lit_info

(** {6 Creation of Literals} *)


(** This function creates a new literal *)

val lit_mk_literal : Signature.signature -> 'a xterm -> bool -> string -> 'a lit_literal

(** Given a term, this function creates a new positive literal of form term=Top *)

val lit_mk_pos_literal : Signature.signature -> 'a xterm -> 'a lit_literal

(** Given a term, this function creates a new negative literal of form term=Bot *)

val lit_mk_neg_literal : Signature.signature -> 'a xterm -> 'a lit_literal

(** Given a term, this function creates a new negative literal of form (term1 = term2) =Bot *)

val lit_mk_uni_literal : Signature.signature -> 'a xterm -> 'a xterm -> lit_info -> 'a lit_literal

(** Given a term, this function creates a new positive  literal of form (term1 = term2) =Top *)

val lit_mk_eq_literal : Signature.signature -> 'a xterm -> 'a xterm -> lit_info -> 'a lit_literal

(** Test for flex flex unification literals *)

val is_flexflex_unilit : 'a lit_literal -> bool 

(** Test for unification literals *)

val is_unilit : 'a lit_literal -> bool 

(** Test for flexible literals *)

val is_flex_lit : 'a lit_literal -> bool 

(** {6 Manipulation of Literals} *)

(** Comparison of literals *)

val lit_compare : 'a lit_literal -> 'a lit_literal -> int

(** A string representation for literals *)

val lit_literal_to_string : 'a lit_literal ->  string

val lit_litlist_to_string : 'a lit_literal list ->  string

(** A POST representation for literals *)

val lit_literal_to_post : 'a lit_literal -> string

val lit_litlist_to_post : 'a lit_literal list -> string

(** A protocol representation for literals *)

val lit_literal_to_protocol : 'a lit_literal -> string

val lit_literal_to_thf : 'a lit_literal -> string

val lit_litlist_to_protocol : 'a lit_literal list ->  string

val lit_litlist_to_thf : 'a lit_literal list ->  string

(*
(** A FOTPTP CNF representation for literals *)

val lit_literal_to_fotptp_cnf : 'a lit_literal signature -> string

val lit_litlist_to_fotptp_cnf : 'a lit_literal list signature -> string
*)
