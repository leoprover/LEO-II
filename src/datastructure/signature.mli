(* ========================================================================= *)
(* The Signature                                                             *)
(* ========================================================================= *)

(** Module Signature implements HOL signatures.
    @author Arnaud, Chris
    @since 07-06-06*)

open Hol_type
open Term


type signature
(** abstract type of HOL signatures *)

(** classes of symbols in the signature *)
type symbol_class = FixedBT | Typevar | FixedLogicalSymbol | DefinedSymbol | UISymbol


(** {6 Fixed basetypes and logical constants} *)

(** the two fixed base types: *)

val bt_i : hol_type
val bt_o : hol_type
val bt_type : hol_type


(** the primitive logical constants: *)

val interpreted_constants : string list
val ctrue : string
val cfalse : string
val neg : string
val box : string
val diamond : string
val forall : string
val disjunction : string
val equality : string

(** defined logical symbols: *)

val exists : string
val negated_disjunction : string (* ~| *)
val conjunction : string
val negated_conjunction : string (* ~& *)
val implies : string (* => *)
val i_f : string (* <= *)
val iff : string (* <=> *)
val negated_iff : string (* <~> *)
val nequals : string (* != *)
val forall_comb : string
val exists_comb : string

val is_defined_logical_symbol : string -> bool

(** {6 Signature construction} *)

val new_signature : unit -> signature
(** Returns a fresh signature containing base types, logical constants and
    the type variable "X". *)

val copy_signature : signature -> signature
(** [copy_signature sigma] returns a copy of [sigma]. *)

val add_basetype : signature -> string -> unit

val add_type_var : signature -> string -> unit

val add_defined_symbol : ?ty:Hol_type.hol_type option -> signature -> string -> Term.term -> unit

val defined_symbol_set_type : signature -> string -> Hol_type.hol_type -> unit

val add_uninterpreted_symbol : signature -> string -> hol_type -> unit

val addifnew_uninterpreted_symbol : signature -> string -> hol_type -> unit


(** {6 Access functions} *)

val is_basetype_in : signature -> string -> bool

val is_defined_symbol : signature -> string -> bool

val is_fixed_logical_symbol : signature -> string -> bool

val is_uninterpreted_symbol : signature -> string -> bool

val get_defined_symbol : signature -> string -> Term.term

val all_fixed_basetypes : signature -> hol_type list
val problemsupplied_fixed_basetypes : signature -> hol_type list

val all_type_vars : signature ->  string list

val all_fixed_logical_symbols : signature -> (string * hol_type) list

val all_defined_symbols : signature -> (string * (Term.term * Hol_type.hol_type option)) list

val all_defined_symbols_without_logical_symbols : signature -> (string * (Term.term * Hol_type.hol_type option)) list

val all_uninterpreted_symbols : signature -> (string * hol_type) list

val class_of_symbol : signature -> string -> symbol_class option
(** Returns None if symbol is not present in the signature,
    don't know if this is really needed *)

val type_of_symbol : signature -> string -> hol_type
(** Assumes the symbol is defined or uninterpreted and present in the signature *)

val compare_defns : (string * (Term.term * Hol_type.hol_type option)) -> (string * (Term.term * Hol_type.hol_type option)) -> int

(** {6 Pretty Printing} *)

val signature_to_string : signature -> string

val symbol_types_to_thf : signature -> string

val defs_to_thf : signature -> string -> string

val all_defs_names : signature -> string
