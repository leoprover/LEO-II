

type ('a,'b) hashtbl = ('a,'b) Hashtbl.t

type ('a,'b) hash1 = ('a,'b) hashtbl
type ('a,'b,'c) hash2 = ('a, ('b,'c) hash1) hash1
type ('a,'b,'c,'d) hash3 = ('a, ('b,'c,'d) hash2) hash1

module OrderedPoly =
 struct
  type t = int
  let compare x y = Pervasives.compare (Hashtbl.hash x) (Hashtbl.hash y) (* THIS IS BAD!!! *)
 
 end

module IntSet = Set.Make(OrderedInt)
    
type 'a set = IntSet.t

type ('a,'b) sethash1 = ('a,'b set) hash1
type ('a,'b,'c) sethash2 = ('a,'b,'c set) hash2
type ('a,'b,'c,'d) sethash3 = ('a,'b,'c,'d set) hash3


let new_hash () =
  Hashtbl.create 10


let hash1_add (h:('a,'b) hash1) k v =
  Hashtbl.add h k v
    
let hash1_find (h:('a,'b) hash1) k =
  Hashtbl.find h k

    
let hash2_add (h:('a,'b,'c) hash2) k1 k2 v =
  try (
    let h' = hash1_find h k1 in
    hash1_add h' k2 v
      ) with Not_found ->
	let h' = new_hash () in
	let _ = hash1_add h' k2 v in
	hash1_add h k1 h'
	  
let hash2_find (h:('a,'b,'c) hash2) k1 =
  let h' = hash1_find h k1 in
  hash1_find h'

    
let hash3_add (h:('a,'b,'c,'d) hash3) k1 k2 k3 v =
  try (
    let h' = hash1_find h k1 in
    try (
      let h'' = hash1_find h' k2 in
      hash1_add h'' k3 v
	) with Not_found ->
	  let h'' = new_hash () in
	  let _ = hash1_add h'' k3 v in
	  hash1_add h' k2 h''
	    ) with Not_found ->
	      let h' = new_hash () in
	      let _ = hash2_add h' k2 k3 v in
	      hash1_add h k1 h'
		
let hash3_find (h:('a,'b,'c,'d) hash3) k1 =
  let h' = hash1_find h k1 in
  hash2_find h'


let sethash1_add (h:('a,'b) sethash1) k v =
  try (
    let s = Hashtbl.find h k in
    Hashtbl.replace h k (IntSet.add v s)
  ) with Not_found ->
    let s = IntSet.add v (IntSet.empty) in
    Hashtbl.add h k s

    
