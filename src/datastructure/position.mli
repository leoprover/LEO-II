(* ========================================================================= *)
(* Positions and related data structures                                     *)
(* ========================================================================= *)


(** Module Position implements term positons and related data structures.
    @author Frank
    @since 19-05-06*)


(** The type of relative positions. *)
type relpos = Abstraction | Function | Arg


(** A term position is specified by a list of relative positions relpos. This list is
    interpreted as a path from the top term to the subterm at the given position, starting
    with the first list element at the top term.*)
type position = relpos list



type 'a positiondata = NoData | WithData of 'a

(** A positiontable is a datastructure to record information related to term positions. It
    can be interpreted either top-down or bottom-up. Top-down interpretation is used to
    record occurrences of subterms (e.g. all free variables of a term or all occurrences
    of  bound variables with the position relative to their binder). Bottom-up
    interpretation is used to record occurrences of terms within superterms (e.g. all
    superterms in which a term occurs as a subterm at a given position).*)
type 'a positiontable =
    Empty
  | Table of 'a positiontable *
             'a positiontable *
             'a positiontable *
             'a positiondata 


(** {6 Positiontable construction} *)

val new_positiontable : unit -> 'a positiontable
(** Create a new positiontable *)


(** {6 Positiontable manipulation} *)

val new_primitive : 'a -> 'a positiontable
(** Create a new positiontable and insert data at root position *)

val new_application : 'a positiontable -> 'a positiontable -> 'a positiontable
(** Create a new positiontable from the tables of the argument and the
function of an appliction *)

val new_abstraction : 'a positiontable -> 'a positiontable
(** Create a new positiontable from the table of an abstraction's body *)

val insert_at_pos : 'a positiontable  -> position -> 'a -> 'a positiontable
(** Insert a new subterm element at a given position into a positiontable (top-down).
    @param table a table
    @param pos the position
    @param v the value to be inserted*)

val merge: 'a positiontable list -> 'a positiontable
(** Merges a list of positiontable. At each position in the resulting
    positiontable the data associated with that position is that of the
    leftmost positiontable in the list which has data associated to that
    position.*)

val replace: 'a positiontable -> 'a positiontable -> 'a positiontable
(** Replaces positions with data by a new subtree.*)

val modify: 'a positiontable -> ('a -> 'b)  -> 'b positiontable
(** Modifies data in the positiontable.*)

val size_of: 'a positiontable -> int
(** Returns the size, i.e. the number of nodes, of a [positiontable] *)




(** {6 Pretty Printer} *)

val to_string : position -> string
(** Returns a string representation of the given position. *)

val to_tex : ('a -> string) -> 'a positiontable -> string
(** Returns a graphical representation of the PST, in latex pstree syntax; use \usepackage\{pstricks,pst-node,pst-tree\} to compile with latex. *)

val show_all_entries : ('a -> string) -> 'a positiontable -> string
(** Returns a string representation of the positiontable. *)

(** {6 Positiontable lookup} *)

val data_at_pos : 'a positiontable -> position -> 'a
(** Lookup the data at a given position *)

val all_entries : 'a positiontable -> (position * 'a) list
(** Lookup all entries in the positiontable along with the according position. *)

