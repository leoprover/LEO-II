(* ========================================================================= *)
(* Cascaded Hashtables                                                       *)
(* ========================================================================= *)

(** Module Nhash cascaded hashtables
    @author Arnaud
    @since 13-12-06*)


type ('a,'b) hashtbl = ('a,'b) Hashtbl.t

type ('a,'b) hash1 = ('a,'b) hashtbl
type ('a,'b,'c) hash2 = ('a, ('b,'c) hash1) hash1
type ('a,'b,'c,'d) hash3 = ('a, ('b,'c,'d) hash2) hash1

type 'a set

type ('a,'b) sethash1 = ('a,'b set) hash1
type ('a,'b,'c) sethash2 = ('a,'b,'c set) hash2
type ('a,'b,'c,'d) sethash3 = ('a,'b,'c,'d set) hash3

val new_hash : unit -> ('a,'b) hashtbl

val hash1_add : ('a,'b) hash1 -> 'a -> 'b -> unit
val hash1_find : ('a,'b) hash1 -> 'a -> 'b

val hash2_add : ('a,'b,'c) hash2 -> 'a -> 'b -> 'c -> unit
val hash2_find : ('a,'b,'c) hash2 -> 'a -> 'b -> 'c

val hash3_add : ('a,'b,'c,'d) hash3 -> 'a -> 'b -> 'c -> 'd -> unit
val hash3_find : ('a,'b,'c,'d) hash3 -> 'a -> 'b -> 'c -> 'd


