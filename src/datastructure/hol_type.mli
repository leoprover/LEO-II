(* ========================================================================= *)
(* HOL Types                                                                 *)
(* ========================================================================= *)

(** Module Hol_type implements HOL types.
    @author Arnaud, Chris
    @since 07-06-06*)


type hol_type =
    Basetype of string
  | Funtype of hol_type * hol_type
(** The abstract type of HOL types.*)


(** {6 Constructors} *)

val basetype : string -> hol_type
(** basetype constructor *)

val abstr_type : hol_type -> hol_type -> hol_type
(** type of an abstraction with bound var of type1 and abstracted term of type2 *)

val new_typevar : unit -> hol_type
(** Returns a fresh type variable. *)

val mk_polyvar : int -> hol_type
(** [mk_polyvar i] returns the [i]th polymorphic type variable,
    i.e. 0 -> 'A, 1 -> 'B, ... 26 -> 'A1 etc. *)

val mk_funtype : hol_type list -> hol_type -> hol_type
(** mk_funtype [ty1,...,tyn] ty returns the type ty1 -> ... -> tyn -> ty *)


(** {6 Destructors} *)

val dest_basetype : hol_type -> string
(** basetype destructor *)

val dest_funtype : hol_type -> hol_type * hol_type

val appl_type : hol_type -> hol_type -> hol_type
(** type of an application of fun term of type1 to an argument of type2 *)
(* isn't this the same as result_type ? *)

val arg_type : hol_type -> hol_type
(** type of the required argument of an application*)

val result_type : hol_type -> hol_type
(** result type of an application *)

val all_arg_types : hol_type -> hol_type list
(** types of all arguments of a funtype *)

val all_arg_types_up_to_goal_type : hol_type -> hol_type -> bool * (hol_type list)
(** flag (whether successful) and types of all arguments of a funtype up to a given goal type*)

val base_result_type : hol_type -> hol_type
(** base_result_type t1 -> t2 -> ... -> tn returns tn *)

(** {6 Predicates} *)

val is_funtype : hol_type -> bool
(** Checks whether the given type is a function type. *)

val is_basetype : hol_type -> bool
(** Checks whether the given type is a basetype. *)

val is_typevar : hol_type -> bool
(** Checks whether its argument is a type variable.
    Type variables are basetypes whose names start with an upper case letter. *)

val is_polyvar : hol_type -> bool
(** Checks whether its argument is a polymorphic type variable.
    Polymorphic type variables are of the form 'A, 'B, ...
    as returned by [mk_polyvar]. *)

(* typeclash? *)
val is_applicable : hol_type -> hol_type -> bool
(** [is_applicable ty1 ty2] checks if [ty2] is an argument type of [ty1]. *)


(** {6 Type substitutions and syntactic unification of type constraints} *)

val subst : hol_type -> string -> hol_type -> hol_type
(** [subst ty x ty'] substitutes all occurences of [basetype x] by [ty'] in [ty]. *)

val substs : (string * hol_type) list -> hol_type -> hol_type

val decompose_constraint : hol_type * hol_type -> (string * hol_type) list

val occurs : string -> hol_type -> bool
(** [occurs x ty] checks whether [basetype x] occurs in [ty]. *)

exception Unsatisfiable
(** Raised by unify_constraints. *)

val unify_constraints : (hol_type -> bool) -> (hol_type * hol_type) list -> (hol_type * hol_type) list
(** [unify_constraints is_polytypevar c] computes the mgu of the set of equations [c].
    The predicate [is_polytypevar] should return true iff its argument is a type variable
    that has been used to instantiate a polymorphic type variable.
    During the unification, an equation should never have such a type variable as lhs
    if the rhs is atomic. *)

val get_typevars : (hol_type -> bool) -> hol_type -> string list
(** [get_typevars p ty] returns all type variables in [ty] as determined by [p],
    i.e., all basetypes [ty'] occuring in [ty] such that [p ty'] holds. *)

val get_polyvars : hol_type -> string list
(** Returns all polymorphic type variables in the argument. *)

val inst_polyvars : hol_type -> hol_type * string list
(** Instantiates polymorphic type variables in a type by fresh type variables and returns
    the list of generated type variables.
    Example:
      ['A -> ('A -> o)] is transformed into [Xi -> (Xi -> o)]
      where [Xi] is a fresh type variable
*)

val uninst_polyvars : hol_type -> string list -> hol_type
(** The inverse of [inst_polyvars].
    [uninst_polyvars ty vl] assumes that all polymorphic type variables in [ty]
    have been replaced by the type variables contained in [vl] and replaces those
    type variables by polymorphic type variables.
    Example:
      [X1 -> (X1 -> X2)] with [vl=\["X1";"X2"\]] becomes ['A -> ('A -> 'B)]
*)

val minimize_polyvars : hol_type -> hol_type
(** Example:
      ['D -> 'B -> 'C] becomes ['A -> 'B -> 'C]
*)


(** {6 Orderings} *)

val type_ordering : hol_type -> int

val compare : hol_type -> hol_type -> int

val compare_string_type_pair : string * hol_type -> string * hol_type -> int

(** {6 Pretty-printing} *)

val to_string : hol_type -> string
(** Returns a string representation of the given type. *)

val to_fotptp_cnf : hol_type -> string
(** Returns a string representation of the given type, according to some own FOTPTP syntax (needed for at-operator) *)

val to_hotptp : hol_type -> string
(** Returns a string representation of the given type, according to the HOTPTP syntax. *)

val to_post : hol_type -> string
(** Returns a string representation of the given type, according to the POST syntax. *)

