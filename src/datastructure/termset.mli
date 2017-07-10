(* ========================================================================= *)
(* Sets of terms in shared representation                                    *)
(* ========================================================================= *)

(** Module Termset implements sets of terms in term graph representation.
    @author Arnaud
    @since 07-06-06*)

open Hol_type
open Term
open Signature


type id = int
(** must this be an abstract type? *)

type termset
(** abstract type of term sets *)

type nodestruct =
  Symbol_node of string |
  Appl_node of id * id |
  Abstr_node of hol_type * id |
  Bound_node of hol_type * int
(** the structure of a term node *)

type termnode = {
  name : id;
  structure : nodestruct;
}
(** term node *)

module IdSet :
    sig
      type elt = id
      type t
      val empty : t
      val is_empty : t -> bool
      val mem : elt -> t -> bool
      val add : elt -> t -> t
      val singleton : elt -> t
      val remove : elt -> t -> t
      val union : t -> t -> t
      val inter : t -> t -> t
      val diff : t -> t -> t
      val compare : t -> t -> int
      val equal : t -> t -> bool
      val subset : t -> t -> bool
      val iter : (elt -> unit) -> t -> unit
      val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
      val for_all : (elt -> bool) -> t -> bool
      val exists : (elt -> bool) -> t -> bool
      val filter : (elt -> bool) -> t -> t
      val partition : (elt -> bool) -> t -> t * t
      val cardinal : t -> int
      val elements : t -> elt list
      val min_elt : t -> elt
      val max_elt : t -> elt
      val choose : t -> elt
      val split : elt -> t -> t * bool * t
    end


type 'a termindex = {
  termbase       : termset;
  occurrences    : (id, (id, id Position.positiontable) Hashtbl.t) Hashtbl.t;
  headsymbol     : (id, id) Hashtbl.t;
  headpos        : (id, Position.position) Hashtbl.t;
  occurs_in      : (id, id) Hashtbl.t;
  has_headsymbol : (id, id) Hashtbl.t;
  boundvars      : (id, int Position.positiontable list) Hashtbl.t;
  boundoffset    : (id, int) Hashtbl.t;
  freevars       : (id, IdSet.t) Hashtbl.t;


(* indexing terms with roles *)
  role                : (id, 'a) Hashtbl.t;
  has_role            : ('a, id) Hashtbl.t;
  occurs_in_role      : (id, IdSet.t) Hashtbl.t;
  role_has_headsymbol : (id, 'a) Hashtbl.t;
  term_at_pos_role    : (Position.position, ((id, IdSet.t) Hashtbl.t)) Hashtbl.t
}
(** a datastructure for term indexing *)



val type_of : 'a termindex -> id -> hol_type


type dot_config = {
  mutable show_node_id : bool;
  mutable show_node_type : bool;
  mutable show_abstr_type : bool;
  mutable show_bound_type : bool;
  mutable show_appl_term : bool;
  mutable node_font_size : int;
  mutable edge_font_size : int
}
(** allows to customize the output of [to_dot] *)

val default_dot_config : dot_config
val set_signature : signature -> unit
(** Set a global signature. This signature is used by [create]
    to look up types of symbols. *)

val get_signature : unit -> signature

val new_termset : unit -> termset
(** returns an empty term set *)

val termset_size : termset -> int
(** returns the number of nodes in the termset *)

val new_index : termset -> 'a termindex
(** returns a new empty index for a termset *)

val is_indexed : id -> 'a termindex -> bool
(** true if [id] is indexed in [idx] *)

val is_used_in_index : id -> 'a termindex -> bool
(** true if [id] occurs in some other term in [idx] *)

val index_node : id -> 'a termindex -> unit
(** record a subterm node in the index *)

val unindex_node : id -> 'a termindex -> unit
(** remove a subterm node from the index *)

val index_term : term -> 'a termindex -> id
(** record a term node in the index *)

val index_with_role : 'a termindex -> term -> 'a -> id
(** record a term node in the index and assign it a role *)

val set_role : 'a termindex -> id -> 'a -> unit
(** assigns a role to a term node *)

val unset_role : 'a termindex -> 'a -> unit
(** removes a role from the index *)

val clear_role_index : 'a termindex -> unit
(** clears all indexed roles *)

val headsymbol_of : id -> 'a termindex -> id
(** returns the headsymbol of a term node *)

val beta_reducable : id -> 'a termindex -> int Position.positiontable
(** positions of all bound variables to be replaced when beta reducing *)

val all_beta_reducable : id -> 'a termindex -> (int Position.positiontable) list
(** positions of all bound variables to be replaced when beta reducing *)

val occurrences : id -> id -> 'a termindex -> int Position.positiontable
(** positions of all occurrences of [id2] in [id1], if there are any *)

val occurs_in : id -> 'a termindex -> id list
(** all terms [id2] in which [id1] occurs in *)

val occurs_at : Position.position ->id -> 'a termindex -> id
(** The subterm [id2] in which [id1] occurs at position [pos] *)


val get_node : termset -> id -> termnode
(** get node by id *)

val nstruct : 'a termindex -> id -> nodestruct
(** get node structure by id *)

val remove_node : termset -> id -> unit
(** removes a node from the termset, along with all
    nodes which are only referenced by this node *)

val replace_node : termset -> id -> id -> unit
(** replaces globally a node by another node *)

val insert : termset -> nodestruct -> id
(** insert a node *)

val insert_and_index : 'a termindex -> nodestruct -> id
(** insert a node into the indexes termbase and index it *)

val create : termset -> term -> id
(** inserts a term into the term graph (which is modified in place)
    and returns the id of the node which represents the term in the
    term graph *)

(*val current_node_type : termset -> id -> hol_type*)

val retrieve : termset -> id -> term
(** returns the term a the node referenced by the id *)

val appl_with_argument : termset -> id -> id -> id

val appl_with_function : termset -> id -> id -> id

val abstr_with_type : termset -> id -> hol_type -> id

val appl_exists : termset -> id -> id -> bool

val abstr_exists : termset -> id -> hol_type -> bool


val term_at_pos : 'a termindex -> id -> Position.position -> id
(** Return the subterm at position [pos] in term [id] *)

val node_type : termset -> id -> hol_type
(** Return the type associated with a node.
    Node types are computed during [create]. *)

val get_instantiation : termset -> id -> (string * hol_type) list
(** [get_instantiation ts id] returns the list of polyvar-type pairs that corresponds
    to the instantiation of polymorphic type variables induced by the application at node [id].
    It will return the empty list whenever [id] does not represent an application, or the application
    at [id] does not instantiate any polymorphic type variables.
    Example: if the termset [ts] is
    0: symbol exists : ('A>$o)>$o
    1: symbol true   : $o
    2: abstr($i,1)   : $i>$o
    3: appl(0,2)     : $o
    then [get_instantiation ts 3 = \[("'A",$i)\]] *)

val eta_expand : signature -> termset -> id -> id
(** Eta-expands the given term. *)

val size_of_term : termset -> id -> int
(** Returns the size of the term *)

val symbol2id : 'a termindex -> string -> id
(** The [id] of a symbol [s] in index [idx] *)

val term_to_string : termset -> id -> string
(** Returns a string representation of the term. *)

val term_to_hotptp : termset -> id -> string
(** Returns a HOTPTP representation of the term. *)

val find_equals : 'a termindex -> id -> ('a -> string) -> string list -> IdSet.t
(** find terms which equal [id] *)

val equality_classes : 'a termindex -> ('a -> string) -> string list -> IdSet.t list
(** equality classes in [idx] *)

val inspect_node : 'a termindex -> id -> ('a -> string) -> string
(** Inspects a node in the index *)

val inspect_symbol : 'a termindex -> string -> ('a -> string) -> string
(** Inspects a symbol in the index *)

val to_string : termset -> string
(** Returns a string representation of the given termset. *)

val node_to_tex : termset -> id -> string
(** Returns a graphical representation of the tree of the given node, in latex pstree syntax; use \usepackage\{pstricks,pst-node,pst-tree\} to compile with latex.
    TODO (someday): change to : termset -> id list -> string *)

val to_dot : ?dc:dot_config -> ?range:(int * int) list -> ?draw_closure:bool -> termset -> string
(** Returns a graph representation of the index in the DOT format. *)

val analyze_termset : 'a termindex -> unit
(** Prints an analysis of the termset *)

val analyze_termset_males : 'a termindex -> unit
(** Prints an analysis of the termset ins a secial way as required for MALES *)

(*val make_termordering : termset -> (hol_type -> int) -> (string -> int) -> id -> (int * int)*)



