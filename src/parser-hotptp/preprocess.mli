(* ========================================================================= *)
(* TPTP preprocessor                                                         *)
(* ========================================================================= *)

(** Module Preprocess implements preprocessing for TPTP problem files
   @author Arnaud 
   @since 13-05-07 *)


val expand_includes : string -> string -> unit
(** [expand_includes infile outfile] reads the TPTP file [infile] and recursively
    expands all "include"-statements. *)


