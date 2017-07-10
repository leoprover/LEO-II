(* ========================================================================= *)
(* Substitutions                                                             *)
(* ========================================================================= *)

(** Module Substitution implements substitutions and their application.
    @author Frank
    @since 31-08-06*)

open Hol_type
open Term
open Signature
open Termset
open Position

type replacement = id positiontable
(** A positiontable with terms to be replaced at the respective positions.*)

type substitution = (id*id) list
(** Substitution *)

val apply_replace : termset -> id -> replacement -> id
(** Apply a replacement to a term *)

val replace_by_fun : termset -> id -> 'a positiontable -> ('a -> id -> id) -> id
(** Apply a replacement to a term *)

val apply_subst : 'a termindex -> substitution -> id -> id
(** Apply a substitution *)

val normalize_appl : 'a termindex -> id -> id -> id
(** Beta-Normalize the application [(t1 t2)] *)

