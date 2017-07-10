
(** Module Darray implements dynamic arrays
    @author Arnaud
    @since 28-05-06*)


type 'a darray
(** The type of dynamic arrays containing elements of type ['a]. *)


val da_make   : int -> 'a -> 'a darray
(** [da_make n x] returns a fresh dynamic array of length [n], initialized with [x]. *)

val da_insert : 'a darray -> 'a -> int
(** [da_insert a x] modifies [a] in place, adding element [x] and returning its index. *)

val da_remove : 'a darray -> int -> unit
(** [da_remove a i] removes the element a position [i] from [a], assuming [i] is a valid
    position in [a]. It does nothing if [i] is not occupied. *)

val da_next_free : 'a darray -> int
(** [da_next_free a] returns the next free position in [a].
    Invariant: [da_insert] always inserts at (and returns) the previous [da_next_free] position. *)

val da_iteri : (int -> 'a -> unit) -> 'a darray -> unit
(** Same as [Array.iteri] *)

val da_copy   : 'a darray -> 'a darray
(** [da_copy a] returns a copy of [a]. *)

val array2da  : 'a array -> 'a darray
(** [array2da a] builds a new dynamic array containing the same elements as [a]. *)

val da2array  : 'a darray -> 'a array
(** [da2array a] returns an array representation of [a]. *)

val da_get    : 'a darray -> int -> 'a
(** [da_get a n] returns the element number [n] of [a]. The first element has number 0. The last element has number [da_size a - 1]. *)

val da_set    : 'a darray -> int -> 'a -> unit
(** [da_set a n x] modifies [a] in place, replacing element number [n] with [x]. *)

val da_size   : 'a darray -> int
(** [da_size a] returns the size (number of elements) of [a]. *)

