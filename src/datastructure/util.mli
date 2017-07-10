val debuglevel : int ref
val sysout : int -> string -> unit
(*val tmpfiles : string list ref*)
module StringSet :
  sig
    type elt = String.t
    type t = Set.Make(String).t
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
IFDEF DEBUG THEN
val tmpfiles : string list ref
ELSE
val tmpfiles : StringSet.t ref
END
val register_tmpfile : string -> unit
val register_tmpfiles : string list -> unit

val try_delete_file : string -> unit
val delete_all_tmpfiles : unit -> unit

val tmp_path : string ref

val add_list : ('a, 'b) Hashtbl.t -> 'c -> 'a -> 'b -> unit
val add_elem : ('a, 'b list) Hashtbl.t -> 'a -> 'b -> unit
val remove_list : ('a, 'b) Hashtbl.t -> 'a -> unit
val remove_elem : ('a, 'b list) Hashtbl.t -> 'a -> 'b -> unit
val remove_elem2 : ('a, 'b list) Hashtbl.t -> 'a -> 'b -> unit
val remove_element3: ('a, 'b) Hashtbl.t -> 'a -> 'b -> unit
val replace_element: ('a, 'b) Hashtbl.t -> 'a -> 'b -> 'b -> unit
val concat_unique : 'a list -> 'a list -> 'a list
val iteri : (int -> 'a) -> int -> 'a list
val id : 'a -> 'a
val implode : string -> string list -> string
val clean_symbol : string -> string

(** migrated here from /src/extensions/pa_timed_enabled.ml : *)

val start_timer : string -> unit

val stop_timer : string -> unit

val get_all_totals : unit -> (float * string) list

val child_processes: int list ref
val spawn: string -> int
val waitfor_spawn: string -> int * Unix.process_status
val command: string -> int
val nanny: unit -> int list
val filicide_all: unit -> unit
