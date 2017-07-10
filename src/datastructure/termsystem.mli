
open Hol_type
open Term
open Termset
open Signature

type 'a xterm =
    Explicit of term
  | Indexed of 'a termindex * int

type 'a xintermediate =
 Xsymbol of string * 'a xterm
  | Xappl of 'a xintermediate * 'a xintermediate * 'a xterm
  | Xabstr of 'a xintermediate * hol_type * 'a xintermediate * 'a xterm
  | Xend of 'a xterm



val set_signature : signature -> unit

val get_signature : unit -> signature

val free_vars : 'a xterm -> term list

val get_head_symbol : 'a xterm -> 'a xterm

val new_termset : unit -> termset

val new_index : termset -> 'a termindex

val term2xterm : term -> 'a xterm

val xterm2term : 'a xterm -> term

val xterm2im : 'a xterm -> int -> 'a xintermediate

val im2xterm : 'a xintermediate -> 'a xterm

val im2term : 'a xintermediate -> term



val mk_var : string -> 'a xterm

val mk_const : string -> 'a xterm

val mk_abs : 'a xterm -> hol_type -> 'a xterm -> 'a xterm

val mk_appl : 'a xterm -> 'a xterm -> 'a xterm


val is_symbol : 'a xterm -> bool

val is_variable : 'a xterm -> bool

val is_constant : 'a xterm -> bool

val is_appl : 'a xterm -> bool

val is_abstr : 'a xterm -> bool


val dest_symbol : 'a xterm -> string

val dest_appl : 'a xterm -> 'a xterm * 'a xterm

val dest_abstr : 'a xterm -> string * hol_type * 'a xterm


val is_indexed : 'a xterm -> bool

val index : 'a termindex -> 'a xterm -> 'a xterm

val index_with_role : 'a termindex -> 'a xterm -> 'a -> 'a xterm

val unindex_role : 'a termindex -> 'a -> unit

val clear_role_index : 'a termindex -> unit

val unindex : 'a xterm -> unit

val free_variables : 'a xterm -> string list

val type_of : 'a xterm -> hol_type


val to_string : 'a xterm -> string

val to_hotptp : 'a xterm -> string

val to_post : 'a xterm -> string

val get_id : 'a termindex -> 'a xterm -> Termset.id

val substitute : 'a termindex -> 'a xterm -> ('a xterm * 'a xterm) list -> 'a xterm 

val occurs_in : 'a termindex -> 'a xterm -> 'a xterm -> bool
(** test if [t2] occurs in [t1] *)
