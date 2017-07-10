(* File: minisatinterface.ml *)
(* Author: Chad E Brown *)
(* Created: November 2010 *)

external minisat_init        : int -> unit = "minisat_init";;
external minisat_addLit      : int -> unit = "minisat_addLit";;
external minisat_addClause   : unit -> bool = "minisat_addClause";;
external minisat_addClause1   : int -> bool = "minisat_addClause1";;
external minisat_addClause2   : int -> int -> bool = "minisat_addClause2";;
external minisat_addClause3   : int -> int -> int -> bool = "minisat_addClause3";;
external minisat_search      : unit -> bool = "minisat_search";;
external minisat_search1     : int -> bool = "minisat_search1";;
external minisat_modelValue : int -> int = "modelValue";;

