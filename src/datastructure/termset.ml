(* ========================================================================= *)
(* Sets of terms in shared representation                                    *)
(* ========================================================================= *)

open Hol_type
open Term
open Signature
open Darray
open List
open Position
open Util

type id = int
type ('a,'b) hashtbl = ('a,'b) Hashtbl.t

type nodestruct =
  Symbol_node of string |
  Appl_node of id * id |
  Abstr_node of hol_type * id |
  Bound_node of hol_type * int

type scopevar =
  Boundvar of int * hol_type |
  Appliedvar of term * ((string * scopevar) list)

type termnode = {
  name : id;
  structure : nodestruct;
}

type termset = {
 nodes          : termnode darray;
 term2id        : (nodestruct,id) hashtbl;
 appl_with_arg  : (id, (id,id) hashtbl) hashtbl;
 appl_with_func : (id, (id,id) hashtbl) hashtbl;
 abstr_with     : (id, (hol_type,id) hashtbl) hashtbl;
 nodetypes      : (id,hol_type) hashtbl;
 uninst_pvs : (id, (string,id) hashtbl) hashtbl;
 inst_pvs : (id, (string * hol_type) list) hashtbl;
}

module IdSet = Set.Make
    (struct type t = id
      let compare x y = x - y
    end)

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



(* for function to_dot *)
type dot_config = {
  mutable show_node_id : bool;
  mutable show_node_type : bool;
  mutable show_abstr_type : bool;
  mutable show_bound_type : bool;
  mutable show_appl_term : bool;
  mutable node_font_size : int;
  mutable edge_font_size : int
}

let default_dot_config = {
  show_node_id = true;
  show_node_type =  false;
  show_abstr_type = true;
  show_bound_type = false;
  show_appl_term = false;
  node_font_size = 12;
  edge_font_size = 9
}


let signature = ref (new_signature ())

let set_signature sigma =
  signature := sigma

let get_signature () =
  !signature


let new_termset () =
  let i = 10 in
  {
    nodes = da_make i {name=0; structure=Symbol_node ""};
    term2id = Hashtbl.create i;
    appl_with_arg = Hashtbl.create i;
    appl_with_func = Hashtbl.create i;
    abstr_with = Hashtbl.create i;
    nodetypes = Hashtbl.create i;
    uninst_pvs = Hashtbl.create i;
    inst_pvs = Hashtbl.create i;
  }

let termset_size ts =
  Darray.da_size ts.nodes

let appl_with_argument ts func arg =
  Hashtbl.find (Hashtbl.find ts.appl_with_arg arg) func

let appl_with_function ts arg func =
  Hashtbl.find (Hashtbl.find ts.appl_with_func func) arg

let abstr_with_type ts body typ =
  Hashtbl.find (Hashtbl.find ts.abstr_with body) typ

let appl_with_func_exists ts func =
  Hashtbl.mem ts.appl_with_func func

let appl_with_arg_exists ts arg =
  Hashtbl.mem ts.appl_with_arg arg

let abstr_with_body_exists ts body =
  Hashtbl.mem ts.abstr_with body

let appl_exists ts func arg =
  try (
    Hashtbl.mem (Hashtbl.find ts.appl_with_arg arg) func
  ) with _ -> false

let abstr_exists ts body typ =
  Hashtbl.mem ts.abstr_with body && Hashtbl.mem (Hashtbl.find ts.abstr_with body) typ

let new_abstraction ts body typ id =
  if Hashtbl.mem ts.abstr_with body
  then Hashtbl.add (Hashtbl.find ts.abstr_with body) typ id
  else let ht = Hashtbl.create 1 in
       Hashtbl.add ht typ id;
       Hashtbl.add ts.abstr_with body ht



let node_exists ts id =
  try (
    ignore (da_get ts.nodes id);
    true
  ) with _ -> false


let supernodes ts id =
  let super=ref 0 in
  if Hashtbl.mem ts.appl_with_func id then super:=!super + (Hashtbl.length (Hashtbl.find ts.appl_with_func id));
  if Hashtbl.mem ts.appl_with_arg id then super:=!super + (Hashtbl.length (Hashtbl.find ts.appl_with_arg id));
  if Hashtbl.mem ts.abstr_with id then super:=!super + (Hashtbl.length (Hashtbl.find ts.abstr_with id));
  !super

let is_used_in_graph ts id =
  (appl_with_func_exists ts id) ||
  (appl_with_arg_exists ts id) ||
  (abstr_with_body_exists ts id)


(** create a new node *)
let make_node name structure =
  { name = name;
    structure = structure }

(** get node by id *)
let get_node ts id =
  da_get ts.nodes id

(** set node by id *)
let set_node ts id node =
  da_set ts.nodes id node


(** remove a node from the term graph *)
let rec remove_node ts id =
  if (not (is_used_in_graph ts id)) then
  let node = get_node ts id in
  Hashtbl.remove ts.term2id node.structure;
  Hashtbl.remove ts.nodetypes id;
  let _ = match node.structure with
      Abstr_node (ty,id1) ->
          let ht = Hashtbl.find ts.abstr_with id1 in
          Hashtbl.remove ht ty;
          if (Hashtbl.length ht) = 0 then
          Hashtbl.remove ts.abstr_with id1;
          remove_node ts id1
    | Appl_node(id1,id2) ->
          let ht1 = Hashtbl.find ts.appl_with_func id1 in
          let ht2 = Hashtbl.find ts.appl_with_arg id2 in
          Hashtbl.remove ht1 id2;
          (if Hashtbl.length ht1 = 0 then Hashtbl.remove ts.appl_with_func id1);
          Hashtbl.remove ht2 id1;
          (if Hashtbl.length ht2 = 0 then Hashtbl.remove ts.appl_with_arg id2);
          remove_node ts id1;
          remove_node ts id2
    | _ -> ()
  in
  da_remove ts.nodes id







(** replace a node in the term graph *)
let rec replace_node ts id id' =
  let _ = get_node ts id in
  let _ = get_node ts id' in
  (if Hashtbl.mem ts.abstr_with id then
    let ht = Hashtbl.find ts.abstr_with id in
    Hashtbl.iter
      (fun a b -> set_node ts b {name=b; structure=Abstr_node (a,id')})
    ht;
    if Hashtbl.mem ts.abstr_with id'
    then let ht' = Hashtbl.find ts.abstr_with id' in
      Hashtbl.iter (fun a b -> Hashtbl.add ht' a b) ht
    else Hashtbl.add ts.abstr_with id' ht);
  (if Hashtbl.mem ts.appl_with_func id then
    let ht = Hashtbl.find ts.appl_with_func id in
    Hashtbl.iter
      (fun a b -> set_node ts b {name=b; structure=Appl_node (id', a)})
    ht;
    if Hashtbl.mem ts.appl_with_func id'
    then let ht' = Hashtbl.find ts.appl_with_func id' in
      Hashtbl.iter (fun a b -> Hashtbl.add ht' a b) ht
    else Hashtbl.add ts.appl_with_func id' ht);
  (if Hashtbl.mem ts.appl_with_arg id then
    let ht = Hashtbl.find ts.appl_with_arg id in
    Hashtbl.iter
      (fun a b -> set_node ts b {name=b; structure=Appl_node (a, id')})
    ht;
    if Hashtbl.mem ts.appl_with_arg id'
    then let ht' = Hashtbl.find ts.appl_with_arg id' in
      Hashtbl.iter (fun a b -> Hashtbl.add ht' a b) ht
    else Hashtbl.add ts.appl_with_arg id' ht);
  Hashtbl.remove ts.abstr_with id;
  Hashtbl.remove ts.appl_with_func id;
  Hashtbl.remove ts.appl_with_arg id;
  remove_node ts id


let nstruct idx id = (get_node idx.termbase id).structure

let rec retrieve' ts id d bound =
  if (node_exists ts id) then
  match (da_get ts.nodes id).structure with
    Symbol_node s -> Symbol s
  | Appl_node (id1,id2) -> Appl(retrieve' ts id1 d bound, retrieve' ts id2 d bound)
  | Abstr_node (ty,id1) ->
          (* deBruijn -> varname may be done by custom function *)
          let var_name = "SX" ^ (string_of_int (d+1)) in
          Abstr(Symbol var_name, ty, retrieve' ts id1 (d+1) ((d+1,var_name)::bound))
  | Bound_node (_,idx) ->
 (*         assert(mem_assoc idx bound);*)
          if mem_assoc idx bound then
          Symbol(assoc (d-idx) bound)
          else Symbol("SX"^(string_of_int (((List.length bound)-idx)-1)))
  else raise Not_found

let retrieve ts id = retrieve' ts id (-1) []

let type_of idx t =
 try 
   Hashtbl.find idx.termbase.nodetypes t
 with _ -> Basetype "'A" (* failwith ("Term  "^(Term.to_hotptp (retrieve idx.termbase t))^" has no type.\n") *)


(** create a new index *)
let new_index ts =
  (* arbitrary initial value *)
  let i = 10 in
  {
    termbase = ts;
    occurrences    = Hashtbl.create i;
    headsymbol     = Hashtbl.create i;
    headpos        = Hashtbl.create i;
    occurs_in      = Hashtbl.create i;
    has_headsymbol = Hashtbl.create i;
    boundvars      = Hashtbl.create i;
    boundoffset    = Hashtbl.create i;
    freevars       = Hashtbl.create i;


    role           = Hashtbl.create i;
    has_role       = Hashtbl.create i;
    occurs_in_role = Hashtbl.create i;
    role_has_headsymbol = Hashtbl.create i;
    term_at_pos_role = Hashtbl.create i;
  }

let headsymbol_of id1 idx =
  if Hashtbl.mem idx.headsymbol id1
  then Hashtbl.find idx.headsymbol id1
  else raise Not_found

let headposition_of id1 idx =
  if Hashtbl.mem idx.headpos id1
  then Hashtbl.find idx.headpos id1
  else raise Not_found

let is_indexed id1 idx = (Hashtbl.mem idx.headsymbol id1)

let is_used_in_index id1 idx = (Hashtbl.mem idx.occurs_in id1)

let rec index_node id1 idx =
  if not (is_indexed id1 idx)
  then
    (* a new Hashtbl to record subterms in id1 *)
    let oc = Hashtbl.create 10 in
    let node = (get_node idx.termbase id1).structure in
    let hs = (match node with
              Abstr_node (_,id2)  -> (index_node id2 idx;
                                      Hashtbl.add idx.freevars id1 (Hashtbl.find idx.freevars id2);
                                      Hashtbl.iter
                                        (fun a b -> Hashtbl.add oc a (Position.new_abstraction b);
                                                    Hashtbl.add idx.occurs_in a id1)
                                        (Hashtbl.find idx.occurrences id2);
                                      Hashtbl.add idx.headpos id1 (Abstraction::(headposition_of id2 idx));
                                      if Hashtbl.mem idx.boundvars id2
                                      then
                                        (Hashtbl.add idx.boundvars id1
                                           (List.map
                                             (fun a -> match a with
                                                         Empty -> Empty |
                                                         _ -> (Table(a,Empty,Empty,NoData)))
                                             (Hashtbl.find idx.boundvars id2));
                                         Hashtbl.add idx.boundoffset
                                         id1 ((Hashtbl.find idx.boundoffset id2)+1));
                                      headsymbol_of id2 idx)|
              Appl_node (id2,id3) -> (index_node id2 idx;
                                      index_node id3 idx;
                                      Hashtbl.add idx.freevars id1 (IdSet.union (Hashtbl.find idx.freevars id2) (Hashtbl.find idx.freevars id2));
                                      let oc2 = Hashtbl.find idx.occurrences id2 in
                                      let oc3 = Hashtbl.find idx.occurrences id3 in
                                      Hashtbl.iter
                                        (fun a b -> let argtbl = if Hashtbl.mem oc3 a
                                                                 then Hashtbl.find oc3 a
                                                                 else Empty in
                                                    Hashtbl.add oc a (Position.new_application b argtbl);
                                                    Hashtbl.add idx.occurs_in a id1)
                                        oc2;
                                      Hashtbl.iter
                                        (fun a b -> if not (Hashtbl.mem oc a) then
                                                    (Hashtbl.add oc a (Position.new_application Empty b);
                                                     Hashtbl.add idx.occurs_in a id1))
                                        oc3;
                                      Hashtbl.add idx.headpos id1 (Function::(headposition_of id2 idx));
                                      let (bv2,bo2) = if Hashtbl.mem idx.boundvars id2
                                                      then (Hashtbl.find idx.boundvars id2,
                                                            Hashtbl.find idx.boundoffset id2)
                                                      else ([],0) in
                                      let (bv3,bo3) = if Hashtbl.mem idx.boundvars id3
                                                      then (Hashtbl.find idx.boundvars id3,
                                                            Hashtbl.find idx.boundoffset id3)
                                                      else ([],0) in
                                      if bv2 <> [] then
                                        if bv3 = []
                                        then (Hashtbl.add idx.boundvars id1
                                               (List.map
                                                 (fun a -> match a with
                                                         Empty -> Empty |
                                                         _ -> (Table(Empty,a,Empty,NoData)))
                                                 (Hashtbl.find idx.boundvars id2));
                                          Hashtbl.add idx.boundoffset
                                          id1 (Hashtbl.find idx.boundoffset id2))
                                        else let (min,max)= ((if bo2<bo3 then bo2 else bo3),
                                                            (let bl2=List.length bv2 in
                                                             let bl3=List.length bv3 in
                                                             (if bo2+bl2>bo3+bl3
                                                               then bo2+bl2 else bo3+bl3)-1)) in
                                             let rec bm m1 m2 = let pt2 = if m1-bo2<(List.length bv2) && m1>=bo2
                                                                      then List.nth bv2 (m1-bo2)
                                                                      else Empty in
                                                            let pt3 = if m1-bo3<(List.length bv3) && m1>=bo3
                                                                      then List.nth bv3 (m1-bo3)
                                                                      else Empty in
                                                            (match pt2,pt3 with
                                                               (Empty,Empty) -> Empty |
                                                               (_,_) -> (Table(Empty,pt2,pt3,NoData)))::
                                                            (if m1<m2 then (bm (m1+1) m2) else [])
                                               in
                                             Hashtbl.add idx.boundvars id1 (bm min max);
                                             Hashtbl.add idx.boundoffset id1 min
                                      else if bv3 <> [] then
                                          (Hashtbl.add idx.boundvars id1
                                               (List.map
                                                 (fun a -> match a with
                                                         Empty -> Empty |
                                                         _ -> (Table(Empty,Empty,a,NoData)))
                                                 (Hashtbl.find idx.boundvars id3));
                                           Hashtbl.add idx.boundoffset
                                           id1 (Hashtbl.find idx.boundoffset id3));
                                      headsymbol_of id2 idx)|
               Symbol_node(s) -> (Hashtbl.add idx.headpos id1 [];
                                  Hashtbl.add idx.freevars id1 (if Term.is_variable (Symbol s) then (IdSet.singleton id1) else IdSet.empty);
                                  id1) |
             Bound_node(ty,i) -> (Hashtbl.add idx.boundoffset id1 (-i);
                                  Hashtbl.add idx.freevars id1 IdSet.empty;
                                  Hashtbl.add idx.boundvars id1 [(Table(Empty,Empty,Empty,WithData(i)))];
                                  Hashtbl.add idx.headpos id1 [];
                                  id1))
          in
    Hashtbl.add oc id1 (Position.new_primitive id1);
    Hashtbl.add idx.occurrences id1 oc;
    Hashtbl.add idx.headsymbol id1 hs;
    Hashtbl.add idx.has_headsymbol hs id1


let unindex_node id idx =
  if not (is_used_in_index id idx) then
  if (is_indexed id idx) then
  if Hashtbl.mem idx.occurrences id then
    Hashtbl.iter
    (fun x _ -> remove_element3 idx.occurs_in x id)
    (Hashtbl.find idx.occurrences id);
  let hs = Hashtbl.find idx.headsymbol id in
  remove_element3 idx.has_headsymbol hs id;
  Hashtbl.remove idx.occurrences id;
  Hashtbl.remove idx.headsymbol id;
  Hashtbl.remove idx.occurs_in id;
  Hashtbl.remove idx.boundvars id;
  Hashtbl.remove idx.boundoffset id


let replace_in_index id id' idx =
  failwith "Not implemented yet"



let beta_reducable id idx = if Hashtbl.mem idx.boundvars id then
                               (let bo=Hashtbl.find idx.boundoffset id in
                                let bv=Hashtbl.find idx.boundvars id in
                                let bl=List.length bv in
                                if bo<=0 && bo+bl>0
                                then List.nth bv (-bo)
                                else Empty)
                            else Empty

let all_beta_reducable id idx = if Hashtbl.mem idx.boundvars id then
                                   (let bo=Hashtbl.find idx.boundoffset id in
                                    let bv=Hashtbl.find idx.boundvars id in
                                    let bl=List.length bv in
                                    let rec fill_list l b = if b < 1 then fill_list (Empty::l) (b+1) else l in
                                    let rec chop_tl l o = if l=[] then []
                                                          else if o<=0 then (hd l)::(chop_tl (tl l) (o+1))
                                                          else []
                                    in
                                    if bo<=0
                                    then fill_list (List.rev (chop_tl bv bo)) (bo+bl)
                                    else [])
                                else []

let occurrences id1 id2 idx = if Hashtbl.mem idx.occurrences id1 then
                                 (let oc=Hashtbl.find idx.occurrences id1 in
                                  if Hashtbl.mem oc id2 then
                                  Hashtbl.find oc id2
                                  else Empty)
                              else Empty

let occurs_in id idx = Hashtbl.find_all idx.occurs_in id

let rec occurs_at pos id idx =
  match (pos,nstruct idx id) with
    [],_ -> id
  | Function::posr,Appl_node (id1,_) -> occurs_at posr id1 idx
  | Arg::posr,Appl_node (_,id2) -> occurs_at posr id2 idx
  | Abstraction::posr,Abstr_node (_,id1) -> occurs_at posr id1 idx
  | _ -> raise (Failure "???")                           


let is_symbol_node ts id =
  match (get_node ts id).structure with
      Symbol_node _ -> true
    | _ -> false


let to_string ts =
  let ty id =
    try (
      Hol_type.to_hotptp (Hashtbl.find ts.nodetypes id))
    with Not_found -> "?"
  in
  let ns = function
      Symbol_node s -> "symbol "^s
    | Appl_node (id1,id2) -> "appl("^(string_of_int id1)^","^(string_of_int id2)^")"
    | Abstr_node (ty,id) -> "abstr("^(Hol_type.to_hotptp ty)^","^(string_of_int id)^")"
    | Bound_node (ty,idx) -> "bound("^(Hol_type.to_hotptp ty)^","^(string_of_int idx)^")"
  in
  let nodearray = da2array ts.nodes in
  let s = ref "" in
  for i = 0 to Array.length nodearray -1 do
    let node = nodearray.(i) in
    (*s := !s ^ (string_of_int node.name) ^ ": "^(ns node.structure)^ "   " ^(ty i)^ "\n"*)
    (*s := !s ^ (Printf.sprintf "%2i: %-16s  %s\n" node.name (ns node.structure) (ty i))*)

    s := !s ^ (Printf.sprintf "%4i: %-30s : %-30s" node.name (ns node.structure) (ty node.name))^
              (if (is_used_in_graph ts node.name)
               then (Printf.sprintf "%i parent(s) " (supernodes ts node.name))
               else " ---        ")^
              (if Hashtbl.mem ts.inst_pvs node.name
               then "["^(Util.implode "," (List.map (fun (v,ty) -> (Hol_type.to_hotptp ty)^"/"^v) (Hashtbl.find ts.inst_pvs node.name)))^"]\n"
               else "\n")
    (* s := !s ^ (Printf.sprintf "%2i: %-16s\n" node.name (ns node.structure)) *)
  done;
  !s


let rec term_at_pos idx id pos =
  match (pos,nstruct idx id)  with
    [],_ -> id
  | (Function::pos1),Appl_node(id1,id2) -> term_at_pos idx id1 pos1
  | (Arg::pos1),Appl_node(id1,id2) -> term_at_pos idx id2 pos1
  | (Abstraction::pos1),Abstr_node(_,id1) -> term_at_pos idx id1 pos1
  | _ -> raise Not_found


let term_to_string ts id =
  try (
    Term.to_string (retrieve ts id))
  with Not_found -> "Term not found"

let term_to_hotptp ts id =
  try (
    Term.to_hotptp (retrieve ts id))
  with Not_found -> "Term not found"

let inspect_node idx id role_to_string =
  let parents = ref 0 in
  let occs = ref 0 in
  let show_node id = "  node "^(string_of_int id)^": "^(term_to_hotptp idx.termbase id)^"\n" in
  let output = ref (
  "Inspecting:\n"^(show_node id)) in
  output := (!output)^"Type:\n  "^(
    try (
      Hol_type.to_hotptp (Hashtbl.find idx.termbase.nodetypes id))
    with Not_found -> "?"
  )^"\n";
  output := (!output)^"Structure:\n  "^(
    match (get_node idx.termbase id).structure
    with
      Symbol_node s -> "symbol "^s
    | Appl_node (id1,id2) -> "appl("^(string_of_int id1)^","^(string_of_int id2)^")"
    | Abstr_node (ty,id) -> "abstr("^(Hol_type.to_hotptp ty)^","^(string_of_int id)^")"
    | Bound_node (ty,idx) -> "bound("^(Hol_type.to_hotptp ty)^","^(string_of_int idx)^")"
  )^"\n";
  output := (!output)^
  "Parents:\n"^
  (if (Hashtbl.mem idx.termbase.appl_with_func id)
   then
     (" - as function term:\n"^
       (Hashtbl.fold
         (fun _ b c -> parents := ((!parents)+1);c^(show_node b))
         (Hashtbl.find idx.termbase.appl_with_func id)
         ""))
   else "")^
  (if (Hashtbl.mem idx.termbase.appl_with_arg id)
   then
     (" - as argument term:\n"^
       (Hashtbl.fold
         (fun _ b c -> parents := ((!parents)+1);c^(show_node b))
         (Hashtbl.find idx.termbase.appl_with_arg id)
         ""))
   else "")^
  (if (Hashtbl.mem idx.termbase.abstr_with id)
   then
     (" - as abstraction body:\n"^
       (Hashtbl.fold
         (fun _ b c -> parents := ((!parents)+1);c^(show_node b))
         (Hashtbl.find idx.termbase.abstr_with id)
         ""))
   else "");
  output := (!output)^(if !parents = 0
                       then " no parents\n"
                       else (" total: "^(string_of_int (!parents))^" parents\n"));
  output := (!output)^
  "Occurs in terms indexed with role:\n"^
  (if (Hashtbl.mem idx.occurs_in_role id)
   then (IdSet.fold
           (fun b c -> occs := ((!occs)+1);
                       c^(show_node b)^"   (in "^
                       (role_to_string (Hashtbl.find idx.role b))^")\n")
           (Hashtbl.find idx.occurs_in_role id)
           "")
   else "");
  output := (!output)^(if !occs = 0
                       then " no occurrences\n"
                       else (" total: "^(string_of_int (!occs))^" terms\n"));
  !output


let inspect_symbol idx symbol role_to_string =
  if Hashtbl.mem idx.termbase.term2id (Symbol_node symbol)
  then inspect_node idx (Hashtbl.find idx.termbase.term2id (Symbol_node symbol)) role_to_string
  else "No such symbol is indexed.\n"




(* ------------------------------------------------------------------------- *)
(* val insert : termset -> nodestruct -> id                                  *)
(*                                                                           *)
(* [insert ts term nodestruct] assumes [nodestruct] corresponds to [term],   *)
(* determines a fresh [id] for [nodestruct], inserts [nodestruct] into [ts]  *)
(* and updates all hashtables.                                               *)
(* ------------------------------------------------------------------------- *)



(* dropped (scope management required):
let rec apply_cs v rplc ty =
  match ty with
    Basetype s -> if s=v then rplc else ty
  | Funtype (a,b) -> Funtype ((apply_cs v rplc a),(apply_cs v rplc b))


let unify_types ty1 ty2 =
  print_string ("Unify: "^(Hol_type.to_hotptp ty1)^" and "^(Hol_type.to_hotptp ty2)^".\n");
  let rec unify_ty ty1 ty2 =
    print_string ("  now: "^(Hol_type.to_hotptp ty1)^" and "^(Hol_type.to_hotptp ty2)^".\n");
    match ty1, ty2 with
      Basetype s, _ -> if ty1=ty2 then ([],[])
                    else if is_polyvar ty1 then ([(s,ty2)],[])
                    else if is_polyvar ty2 then ([],[(Hol_type.to_string ty2,ty1)])
                    else failwith ("Type mismatch 1: "^(Hol_type.to_hotptp ty1)^" and "^(Hol_type.to_hotptp ty2)^".\n")
    | Funtype (a,b), Basetype c -> if is_polyvar ty2 then ([],[(Hol_type.to_string ty2,ty1)])
                    else failwith ("Type mismatch 2: "^(Hol_type.to_hotptp ty1)^" and "^(Hol_type.to_hotptp ty2)^".\n")
    | Funtype (a,b), Funtype (c,d) -> let (cl,cr) = unify_ty a c in
                    let (cl2,cr2)= unify_ty (List.fold_left (fun ty (v,rplc) -> apply_cs v rplc ty) b cl)
                                            (List.fold_left (fun ty (v,rplc) -> apply_cs v rplc ty) d cr) in
                    (cl2@cl,cr2@cr)
  in
  unify_ty ty1 ty2 

let application_type ty1 ty2 =
  match ty1 with
    Basetype _ -> if is_polyvar ty1 then Basetype "'A"
                  else failwith ("Not a function type: "^(Hol_type.to_hotptp ty1)^".\n")
  | Funtype (a,b) -> let (cl,cr) = unify_types a ty2 in
                  (List.fold_left (fun ty (v,rplc) -> apply_cs v rplc ty) b cl)
                  
  
*)

let insert ts nodestruct =
  match nodestruct with
    Abstr_node (typ,id1) ->
      if abstr_exists ts id1 typ
      then abstr_with_type ts id1 typ
      else
      let id = da_next_free ts.nodes in
      let _ = da_insert ts.nodes (make_node id nodestruct) in
      let _ = new_abstraction ts id1 typ id in
      let _ =
        try
          let ty1 = Hashtbl.find ts.nodetypes id1 in
          Hashtbl.add ts.nodetypes id (abstr_type typ ty1)
        with _ ->
          (*print_string ("while inserting Abstr_node("^(string_of_int id1)^"):\nnode "^(string_of_int id1)^" has no type\n")*) () in
      id
  | Appl_node (id1,id2) ->
      if appl_exists ts id1 id2
      then appl_with_function ts id2 id1
      else
      let id = da_next_free ts.nodes in
      let _ = da_insert ts.nodes (make_node id nodestruct) in
      let appl_with_func_id1 = ref (Hashtbl.create 10) in
      let _ =
        if Hashtbl.mem ts.appl_with_func id1 then
          appl_with_func_id1 := Hashtbl.find ts.appl_with_func id1 in
      Hashtbl.add !appl_with_func_id1 id2 id;
      Hashtbl.replace ts.appl_with_func id1 !appl_with_func_id1;
      let appl_with_arg_id2 = ref (Hashtbl.create 10) in
      let _ =
        if Hashtbl.mem ts.appl_with_arg id2 then
          appl_with_arg_id2 := Hashtbl.find ts.appl_with_arg id2 in
      Hashtbl.add !appl_with_arg_id2 id1 id;
      Hashtbl.replace ts.appl_with_arg id2 !appl_with_arg_id2;
      

(* dropped (scope management required):
      let ty1 = Hashtbl.find ts.nodetypes id1 in
      let ty2 = Hashtbl.find ts.nodetypes id2 in
      
      let ty1 = try Hashtbl.find ts.nodetypes id1 with _ -> Basetype "*" in
      let ty2 = try Hashtbl.find ts.nodetypes id2 with _ -> Basetype "*" in      
      print_string ((Hol_type.to_hotptp ty1)^" @ "^(Hol_type.to_hotptp ty2)^":\n");
      let ty_appl = application_type ty1 ty2 in
      print_string ((Hol_type.to_hotptp ty_appl)^"\n");
      Hashtbl.add ts.nodetypes id ty_appl;
*)








      let _ =
        try (
          try (
            let ty1 = Hashtbl.find ts.nodetypes id1 in
            try (
              let ty2 = Hashtbl.find ts.nodetypes id2 in
              if is_funtype ty1 then
                let (ty11,ty12) = (arg_type ty1,result_type ty1) in
                if ty11=ty2 then Hashtbl.add ts.nodetypes id ty12
                else
                  let theta = decompose_constraint (ty11,ty2) in
                  try
                    Hashtbl.add ts.nodetypes id (substs theta ty12);
                    let pv1 = get_polyvars ty1 in
                    if Hashtbl.mem ts.uninst_pvs id1
                    then Hashtbl.add ts.uninst_pvs id (Hashtbl.find ts.uninst_pvs id1)
                    else
                      let up_id = Hashtbl.create 10 in
                      let _ = List.iter (fun v -> Hashtbl.add up_id v id) pv1 in
                      Hashtbl.add ts.uninst_pvs id up_id;
                    let up_id = Hashtbl.find ts.uninst_pvs id in
                    List.iter (fun (v,ty) ->
                      let dest_id = Hashtbl.find up_id v in
                      let pair = (v,ty) in
                      if Hashtbl.mem ts.inst_pvs dest_id
                      then Hashtbl.replace ts.inst_pvs dest_id (pair::(Hashtbl.find ts.inst_pvs dest_id))
                      else Hashtbl.add ts.inst_pvs dest_id [pair];
                      Hashtbl.remove up_id v
                    ) theta;
                    Hashtbl.replace ts.uninst_pvs id up_id;
                  with Failure s -> failwith s
                     | _ -> failwith ("argument type mismatch: "^(term_to_hotptp ts id1)^" of type "^(Hol_type.to_string ty1)^
              " applied to "^(term_to_hotptp ts id2)^" of type "^(Hol_type.to_string ty2))
              else failwith "applying a non-function";
            ) with Failure s -> failwith s
                 | _ -> failwith ("node "^(string_of_int id2)^"\n "^(term_to_hotptp ts id2)^" at argument position has no type\n") 
          ) with Failure s -> failwith s
               | _ -> failwith ("node "^(string_of_int id1)^"\n "^(term_to_hotptp ts id1)^" at function position has no type\n");
        ) with Failure s ->
          Util.sysout 1 ("while inserting node "^(string_of_int id)^": Appl_node("^(string_of_int id1)^","^(string_of_int id2)^"):\n"^s^"\n") in
      id
  | Bound_node(typ,i) ->
      if Hashtbl.mem ts.term2id nodestruct
      then Hashtbl.find ts.term2id nodestruct
      else
      let id = da_next_free ts.nodes in
      let _ = da_insert ts.nodes (make_node id nodestruct) in
      Hashtbl.add ts.term2id nodestruct id;
      Hashtbl.add ts.nodetypes id typ;
      id
  | Symbol_node s ->
      if Hashtbl.mem ts.term2id nodestruct
      then Hashtbl.find ts.term2id nodestruct
      else
      let id = da_next_free ts.nodes in
      let _ = da_insert ts.nodes (make_node id nodestruct) in
      Hashtbl.add ts.term2id nodestruct id;
      (try (
        Hashtbl.add ts.nodetypes id (type_of_symbol !signature s)
      ) with Failure _ ->
        let tvar = new_typevar () in
        Hashtbl.add ts.nodetypes id tvar);
      id


(* ---------------------------------------------------------------------------------------------- *)
(* val create' : termset -> term -> int -> (string*(int*hol_type)) list -> (string*id) list -> id *)
(*                                                                                                *)
(* [create' ts t d bound applied] expects                                                         *)
(*   [ts] a termset                                                                               *)
(*   [t] a term                                                                                   *)
(*   [d] the current scope                                                                        *)
(*   [bound] a list mapping symbols to pairs of deBruijn-indices and types                        *)
(*   [applied] a list mapping symbols to IDs for beta-reduction                                   *)
(* ---------------------------------------------------------------------------------------------- *)

let rec create' ts t d scope argstack =
  let rec make_appl id1 d argstack1 =
        (match argstack1 with
           ((Appliedvar(t1,scope_t1))::rest) ->
             let id2 = create' ts t1 d scope_t1 [] in
             let id3 = insert ts (Appl_node (id1,id2)) in
             make_appl id3 d rest
         | _ -> id1)
  in
  match t with
    Symbol s ->
      if mem_assoc s scope
      then
      (match assoc s scope with
         Boundvar (ds,typs) ->
	   let id1 = insert ts (Bound_node (typs, d-ds)) in
           make_appl id1 d argstack
       | Appliedvar (t1,scope_t1) -> create' ts t1 d scope_t1 argstack)
      else let id1 = insert ts (Symbol_node s) in
        make_appl id1 d argstack
  | Appl (t1,t2) -> create' ts t1 d scope (Appliedvar(t2,scope)::argstack)
  | Abstr (x,typx,t1) ->
     assert(is_symbol x);
     (match argstack with
        [] ->
	      let id1 = create' ts t1 (d+1) ((get_symbol x, Boundvar (d+1,typx))::scope) [] in
              let id2 = insert ts (Abstr_node (typx,id1)) in
	      id2
      | (a::arest) -> create' ts t1 d ((get_symbol x, a)::scope) arest)



let create ts t =
  create' ts t (-1) [] []



let index_term t idx =
  let id = create idx.termbase t in
  index_node id idx;
  id

let insert_and_index idx nodestruct =
  let id = insert idx.termbase nodestruct in
  let _ = index_node id idx in
  id


let rec index_role_subterms idx id root role pos =
  if (not (Hashtbl.mem idx.term_at_pos_role pos)) then Hashtbl.add idx.term_at_pos_role pos (Hashtbl.create 3);
  let id2root = Hashtbl.find idx.term_at_pos_role pos in
  let newrootset = if (Hashtbl.mem id2root id) then IdSet.add root (Hashtbl.find id2root id)
                   else IdSet.singleton root in
  Hashtbl.replace (Hashtbl.find idx.term_at_pos_role pos) id newrootset;
  Hashtbl.replace idx.occurs_in_role id (if (Hashtbl.mem idx.occurs_in_role id) then IdSet.add root (Hashtbl.find idx.occurs_in_role id)
                   else IdSet.singleton root);
  (* print_string ((string_of_int id)^" occurs in "^(string_of_int root)^"\n"); *)
  match  nstruct idx id with
    Appl_node (id1,id2) -> (index_role_subterms idx id1 root role (pos@[Function]);
                     index_role_subterms idx id2 root role (pos@[Arg]))
  | Abstr_node (_,id1) -> index_role_subterms idx id1 root role (pos@[Abstraction])
  | _ -> ()

let set_role idx id r =
  Hashtbl.add idx.role id r;
  Hashtbl.add idx.has_role r id;
  Hashtbl.add idx.role_has_headsymbol (Hashtbl.find idx.headsymbol id) r;
  index_role_subterms idx id id r []


let rec unindex_role_subterms idx id root role pos =
  let id2root = Hashtbl.find idx.term_at_pos_role pos in
  let newrootset = if (Hashtbl.mem id2root id) then IdSet.remove root (Hashtbl.find id2root id)
                   else IdSet.empty in
  Hashtbl.replace (Hashtbl.find idx.term_at_pos_role pos) id newrootset;
  Hashtbl.replace idx.occurs_in_role id (if (Hashtbl.mem idx.occurs_in_role id) then IdSet.remove root (Hashtbl.find idx.occurs_in_role id)
                   else IdSet.empty);
  (* print_string ((string_of_int id)^" occurs in "^(string_of_int root)^"\n"); *)
  match  nstruct idx id with
    Appl_node (id1,id2) -> (unindex_role_subterms idx id1 root role (pos@[Function]);
                     unindex_role_subterms idx id2 root role (pos@[Arg]))
  | Abstr_node (_,id1) -> unindex_role_subterms idx id1 root role (pos@[Abstraction])
  | _ -> ()

let unset_role idx r =
  if Hashtbl.mem idx.has_role r then
   (let id = Hashtbl.find idx.has_role r in
    Hashtbl.remove idx.has_role r;
    remove_element3 idx.role id r;
    remove_element3 idx.role_has_headsymbol (Hashtbl.find idx.headsymbol id) r;
    unindex_role_subterms idx id id r [])


let index_with_role idx t r =
  let id = index_term t idx in
  set_role idx id r;
  id


let clear_role_index idx =
    Hashtbl.clear idx.role;
    Hashtbl.clear idx.has_role;
    Hashtbl.clear idx.occurs_in_role;
    Hashtbl.clear idx.role_has_headsymbol;
    Hashtbl.clear idx.term_at_pos_role


let find_role_with_term_at_pos idx id pos =
  if ((Hashtbl.mem idx.term_at_pos_role pos) &&
      (Hashtbl.mem (Hashtbl.find idx.term_at_pos_role pos) id))
  then (Hashtbl.find (Hashtbl.find idx.term_at_pos_role pos) id)
  else IdSet.empty

let find_equalities idx classify use_eq =
  let eq = insert idx.termbase (Symbol_node "=") in
  let allequations = try (Hashtbl.find (Hashtbl.find idx.term_at_pos_role [Function;Function]) eq)
                     with Not_found -> IdSet.empty in
  let equationclasses = Hashtbl.create 5 in
  IdSet.iter (fun eq -> let cls = (classify (Hashtbl.find idx.role eq)) in
                        let set = try Hashtbl.find equationclasses cls
                                  with Not_found -> IdSet.empty in
                        Hashtbl.replace equationclasses cls (IdSet.add eq set))
             allequations;
  let pos_unit = ref IdSet.empty in
  let neg_unit = ref IdSet.empty in
  let tsym = insert idx.termbase (Symbol_node"true") in
  let fsym = insert idx.termbase (Symbol_node "false") in
  let eqsym = insert idx.termbase (Symbol_node "=") in
  let eqt = insert idx.termbase (Appl_node (eqsym,tsym)) in
  let eqf = insert idx.termbase (Appl_node (eqsym,fsym)) in
  Hashtbl.iter (fun id r -> let litcls = classify r in
                            if litcls = "pos_unit" then pos_unit := IdSet.add (insert idx.termbase (Appl_node (eqt,id))) (!pos_unit)
                            else if litcls = "neg_unit" then neg_unit := IdSet.add (insert idx.termbase (Appl_node (eqf,id))) (!neg_unit))
               idx.role;
  let equations = IdSet.union (IdSet.union (!pos_unit) (!neg_unit))
                  (Hashtbl.fold (fun cls set orig_set -> if List.mem cls use_eq
                                                        then IdSet.union set orig_set
                                                        else orig_set)
                   equationclasses IdSet.empty) in
  Hashtbl.add equationclasses "pos_unit_lit" (!pos_unit);
  Hashtbl.add equationclasses "neg_unit_lit" (!neg_unit);
  let term2class = Hashtbl.create (IdSet.cardinal equations) in
  let class2set = Hashtbl.create (IdSet.cardinal equations) in
  let classcount = ref 0 in
  IdSet.iter
    (fun equate ->
       (* print_string ("eq "^(string_of_int equate)^": "^(term_to_hotptp idx.termbase equate)^"\n"); *)
       let id1 = term_at_pos idx equate [Function;Arg] in
       let id2 = term_at_pos idx equate [Arg] in
       try
         let cls1 = Hashtbl.find term2class id1 in
         if Hashtbl.mem term2class id2
         then (let cls2 = Hashtbl.find term2class id2 in
               let set1 = Hashtbl.find class2set cls1 in
               let set2 = Hashtbl.find class2set cls2 in
               (* print_string ("class 1: "^(string_of_int cls1)^"\n"); *)
               (* print_string ("class 2: "^(string_of_int cls2)^"\n"); *)
               Hashtbl.remove class2set cls2;
               IdSet.iter (fun t -> Hashtbl.replace term2class t cls1) set2;
               Hashtbl.replace class2set cls1 (IdSet.union set1 set2))
         else (let set1 = Hashtbl.find class2set cls1 in
               Hashtbl.add term2class id2 cls1;
               (* print_string ("class 1: "^(string_of_int cls1)^"\n"); *)
               Hashtbl.replace class2set cls1 (IdSet.add id2 set1))
       with Not_found ->
       try
         let cls2 = Hashtbl.find term2class id2 in
         let set2 = Hashtbl.find class2set cls2 in
         (* print_string ("class 2: "^(string_of_int cls2)^"\n"); *)
         Hashtbl.add term2class id1 cls2;
         Hashtbl.replace class2set cls2 (IdSet.add id1 set2)
       with Not_found ->
         (* print_string ("new class: "^(string_of_int (!classcount))^"\n"); *)
         Hashtbl.add term2class id1 (!classcount);
         Hashtbl.add term2class id2 (!classcount);
         Hashtbl.add class2set (!classcount) (IdSet.union (IdSet.singleton id1) (IdSet.singleton id2));
         classcount := (!classcount)+1
    )
    equations;
  print_string "Classes of equations:\n";
  Hashtbl.iter (fun cls set -> print_string (cls^":\n");
                               IdSet.iter (fun eq -> print_string ("  eq "^(string_of_int eq)^": "^(term_to_hotptp idx.termbase eq)^"\n"))
                               set)
  equationclasses;
  (term2class,class2set,equationclasses)

let equality_classes idx classify use_eq =
  match find_equalities idx classify use_eq with
    (_,class2set,_) -> Hashtbl.fold (fun _ set l -> set::l) class2set []

let find_equals idx id classify use_eq =
  match find_equalities idx classify use_eq with
    (term2class,class2set,_) -> try Hashtbl.find class2set (Hashtbl.find term2class id)
                              with Not_found -> IdSet.singleton id



let find_equals_one_step idx id =
  let eq = insert idx.termbase (Symbol_node "=") in
  let equations = try (Hashtbl.find (Hashtbl.find idx.term_at_pos_role [Function;Function]) eq)
                  with Not_found -> IdSet.empty in
  let lefthand = try (Hashtbl.find (Hashtbl.find idx.term_at_pos_role [Function;Arg]) id)
                  with Not_found -> IdSet.empty in
  let righthand = try (Hashtbl.find (Hashtbl.find idx.term_at_pos_role [Arg]) id)
                  with Not_found -> IdSet.empty in
  IdSet.fold (fun id s -> IdSet.add (term_at_pos idx id [Arg]) s)
    (IdSet.inter equations lefthand)
  (IdSet.fold (fun id s -> IdSet.add (term_at_pos idx id [Function;Arg]) s)
    (IdSet.inter equations righthand) IdSet.empty)




let node_type ts id =
  Hashtbl.find ts.nodetypes id

let get_instantiation ts id =
  try (Hashtbl.find ts.inst_pvs id)
  with Not_found -> []

let symbol2id idx s =
  insert idx.termbase (Symbol_node s)


let eta_expand sigma ts id =
  let arg_types = all_arg_types (node_type ts id) in
  fold_left (fun id' ty ->
      let applied_var = insert ts (Bound_node (ty,0)) in
      let appl_node = insert ts (Appl_node (id', applied_var)) in
      insert ts (Abstr_node (ty, appl_node)))
  id arg_types


let rec size_of_term ts id =
  match (get_node ts id).structure with
    Symbol_node s -> 1
  | Appl_node (id1,id2) -> (size_of_term ts id1) + (size_of_term ts id2) +1
  | Abstr_node (_,id) -> (size_of_term ts id) +1
  | Bound_node (_,_) -> 1


(*let to_string ts =
  let ty id =
    try (
      Hol_type.to_hotptp (Hashtbl.find ts.nodetypes id))
    with Not_found -> "?"
  in
  let ns = function
      Symbol_node s -> "symbol "^s
    | Appl_node (id1,id2) -> "appl("^(string_of_int id1)^","^(string_of_int id2)^")"
    | Abstr_node (ty,id) -> "abstr("^(Hol_type.to_hotptp ty)^","^(string_of_int id)^")"
    | Bound_node (ty,idx) -> "bound("^(Hol_type.to_hotptp ty)^","^(string_of_int idx)^")"
  in
  let nodearray = da2array ts.nodes in
  let s = ref "" in
  for i = 0 to Array.length nodearray -1 do
    let node = nodearray.(i) in
    (*s := !s ^ (string_of_int node.name) ^ ": "^(ns node.structure)^ "   " ^(ty i)^ "\n"*)
    (*s := !s ^ (Printf.sprintf "%2i: %-16s  %s\n" node.name (ns node.structure) (ty i))*)

    s := !s ^ (Printf.sprintf "%2i: %-16s : %-24s" node.name (ns node.structure) (ty node.name))^
              (if (is_used_in_graph ts node.name)
               then (Printf.sprintf "%i parent(s)\n" (supernodes ts node.name))
               else " ---\n")
    (* s := !s ^ (Printf.sprintf "%2i: %-16s\n" node.name (ns node.structure)) *)
  done;
  !s*)


let escape_tex_chars s =
  let rec replace i =
    if i>=String.length s then "" else
      let r =
        match String.get s i with
            '_' -> "\\_"
          | '^' -> "\\^"
          | '\\' -> "\\\\"
          | '$' -> "\\$"
          | '{' -> "\\{"
          | '}' -> "\\}"
          | '[' -> "\\["
          | ']' -> "\\]"
          | c -> String.make 1 c
       in r^(replace (i+1))
  in replace 0

type drawnode = {
	nodeid : id;
	nodename : string;
	nodestructure : drawnodestruct;
}
and drawnodestruct = Symbol_dnode of string | Appl_dnode of drawnode * drawnode | Abstr_dnode of drawnode | Bound_dnode of int

let pstree_optional_args = "[levelsep=5ex,nodesep=3pt]"

let node_to_tex ts id =
	(* for each id, store list of node labels and correspodoing depth *)
	let idcount = Hashtbl.create 17 in
	(* generate a fresh node label and store it *)
	let new_name d id =
		let l = (
			try (
				Hashtbl.find idcount id
			) with Not_found ->
				let _ = Hashtbl.add idcount id []
				in []) in
		let name = "node"^(string_of_int id)^"_"^(string_of_int (List.length l)) in
		let _ = Hashtbl.replace idcount id ((name,d)::l) in
		name in
	(* traverse the termset and build a tree of type drawnode *)
	let rec make_tree d id =
		let termnode = get_node ts id in
		let name = new_name d id in
		match termnode.structure with
				Symbol_node s ->
						{nodeid=id; nodename=name; nodestructure=Symbol_dnode s}
			| Appl_node (id1,id2) ->
						{nodeid=id; nodename=name; nodestructure=Appl_dnode (make_tree (d+1) id1,make_tree (d+1) id2)}
			| Abstr_node (_,id1) ->
						{nodeid=id; nodename=name; nodestructure=Abstr_dnode (make_tree (d+1) id1)}
			| Bound_node (_,i) ->
						{nodeid=id; nodename=name; nodestructure=Bound_dnode i}
	in
	let tex_nodelabel name id strct =
(*		let l =	match strct with
				Symbol_dnode s -> "$"^s^"^"^(string_of_int id)^"$"
			| Appl_dnode (_,_) -> "$@^"^(string_of_int id)^"$"
			| Abstr_dnode _ -> "$\\lambda^"^(string_of_int id)^"$"
			| Bound_dnode i -> "$x_{"^(string_of_int i)^"}^"^(string_of_int id)^"$"
		in "\\TR[name="^name^"]{~~"^l^"}"*)
		let l =	match strct with
			  Symbol_dnode s -> "{\\footnotesize{"^(string_of_int id)^"}}: "^(escape_tex_chars s)
			| Appl_dnode (_,_) -> "{\\footnotesize{"^(string_of_int id)^"}}: @"
			| Abstr_dnode _ -> "{\\footnotesize{"^(string_of_int id)^"}}: $\\lambda$"
			| Bound_dnode i -> "{\\footnotesize{"^(string_of_int id)^"}}: $x_{"^(string_of_int i)^"}$"
		in "\\TR[name="^name^"]{~~"^l^"}"
	in
	let extra_edges = ref "" in
	(* convert drawnode tree to string, labeling nodes only if they are the deepest occurence of their id *)
	let rec draw_tree d t =
		let w = String.make d ' ' in
		(* sort in descending order of depth *)
		let l = List.sort (fun n n' -> if n' > n then 1 else if n = n' then 0 else -1) (Hashtbl.find idcount t.nodeid) in
		let (deepest_occurence,other_occurences) = (List.hd l, List.tl l) in
		if fst deepest_occurence = t.nodename then
			let _ = List.iter (fun (src,_) ->
								extra_edges := !extra_edges ^ "\\ncline[linestyle=dotted]{"^src^"}{"^(fst deepest_occurence)^"}\n";
							) other_occurences in
			match t.nodestructure with
					Symbol_dnode s ->
							w^(tex_nodelabel t.nodename t.nodeid t.nodestructure)^"\n"
							(*w^"\\TR[name="^t.nodename^"]{"^(string_of_int t.nodeid)^":symbol("^s^")}\n"*)
				| Appl_dnode (n1,n2) ->
							w^"\\pstree"^(if d=0 then pstree_optional_args else "")^"{"^(tex_nodelabel t.nodename t.nodeid t.nodestructure)^"}{\n"
							^(draw_tree (d+1) n1)^(draw_tree (d+1) n2)^w^"}\n"
				| Abstr_dnode (n1) ->
							w^"\\pstree"^(if d=0 then pstree_optional_args else "")^"{"^(tex_nodelabel t.nodename t.nodeid t.nodestructure)^"}{\n"
							^(draw_tree (d+1) n1)^w^"}\n"
				|	Bound_dnode i ->
							w^(tex_nodelabel t.nodename t.nodeid t.nodestructure)^"\n"
		else
			w^"\\TR[name="^t.nodename^"]{}\n"
	in
	let s = draw_tree 0 (make_tree 0 id) in
	s^(!extra_edges)^"\n\n\\vspace{1cm}\n"


(* FIXME: something isn't working *)
let to_dot ?(dc=default_dot_config) ?(range=[]) ?(draw_closure=false) ts =
  let inrange id =
    match range with
        [] -> true
      | xs -> List.fold_left (fun acc (n1,n2) -> acc || (id >= min n1 n2 && id <= max n1 n2)) false xs
  in
  let parents id = (if (Hashtbl.mem ts.appl_with_arg id) then (Hashtbl.length (Hashtbl.find ts.appl_with_arg id)) else 0) +
                   (if (Hashtbl.mem ts.appl_with_func id) then (Hashtbl.length (Hashtbl.find ts.appl_with_func id)) else 0) +
                   (if (Hashtbl.mem ts.abstr_with id) then (Hashtbl.length (Hashtbl.find ts.abstr_with id)) else 0)
  in
  let hty id =
    try (
      Hol_type.to_hotptp (Hashtbl.find ts.nodetypes id))
    with Not_found -> "?"
  in
  let reachable = Hashtbl.create 17 in
  let rec compute_closure id =
    Hashtbl.add reachable id ();
    match (get_node ts id).structure with
        Abstr_node(_,id1) ->
          compute_closure id1
      | Appl_node(id1,id2) ->
          compute_closure id1;
          compute_closure id2
      | _ -> ()
  in
  let nodes = da2array ts.nodes in
  let nodestr = Hashtbl.create 17 in
  let edgestr = Hashtbl.create 17 in
  for i = 0 to Array.length nodes -1 do
    let node = nodes.(i) in
    let nstr = string_of_int node.name in
    let term = retrieve ts node.name in
    if draw_closure && inrange node.name
    then compute_closure node.name
    else ();
    match node.structure with
        Symbol_node s ->
          Hashtbl.add nodestr node.name
            ("  node"^(string_of_int node.name)^" [label=\""^
            (if dc.show_node_id then nstr^": " else "")^s^
            (if dc.show_node_type then " ["^(hty node.name)^"]" else "")^"\"];\n")

      | Appl_node(id1,id2) ->
          Hashtbl.add nodestr node.name
            ("  node"^(string_of_int node.name)^" [label=\""^
            (if dc.show_node_id then nstr^": " else "")^(if dc.show_appl_term then to_compressed term else "@")^
            (if dc.show_node_type then " ["^(hty node.name)^"]" else "")^"\"];\n");
          Hashtbl.add edgestr node.name
            ("  node"^(string_of_int node.name)^" -> node"^(string_of_int id1)^
            " [sametail=node"^(string_of_int node.name)^"t"^
            (if parents id1 > 1 then ",samehead=node"^(string_of_int id1)^"h];\n" else "];\n"), id1);
          Hashtbl.add edgestr node.name
            ("  node"^(string_of_int node.name)^" -> node"^(string_of_int id2)^
            " [arrowhead=onormal,sametail=node"^(string_of_int node.name)^"t"^
            (if parents id2 > 1 then ",samehead=node"^(string_of_int id2)^"h];\n" else "];\n"), id2);

      | Abstr_node(ty,id) ->
          Hashtbl.add nodestr node.name
            ("  node"^(string_of_int node.name)^" [label=\""^
            (if dc.show_node_id then nstr^": " else "")^"^"^
            (if dc.show_abstr_type then "["^(Hol_type.to_hotptp ty)^"]" else "")^
            (if dc.show_node_type then " ["^(hty node.name)^"]" else "")^"\"];\n");
          Hashtbl.add edgestr node.name
            ("  node"^(string_of_int node.name)^" -> node"^(string_of_int id)^
            (if parents id > 1 then "[samehead=node"^(string_of_int id)^"h];\n" else ";\n"), id);

      | Bound_node(ty,j) ->
          Hashtbl.add nodestr node.name
            ("  node"^(string_of_int node.name)^" [label=\""^
            (if dc.show_node_id then nstr^": " else "")^"SX"^(string_of_int j)^
            (if dc.show_bound_type then ":["^(Hol_type.to_hotptp ty)^"]" else "")^
            (if dc.show_node_type then " ["^(hty node.name)^"]" else "")^"\"];\n")
  done;
  "digraph TS {\n  node [shape=plaintext,fontsize="^(string_of_int dc.node_font_size)^
  ", height=0.25,width=0.25];\n  edge [fontsize="^(string_of_int dc.edge_font_size)^"];\n\n"^
  (Hashtbl.fold (fun id str acc ->
    acc^(if inrange id || (draw_closure && Hashtbl.mem reachable id) then str else "")) nodestr "")^"\n"^
  (Hashtbl.fold (fun id (str,target) acc ->
    acc^(if (inrange id && inrange target) || (draw_closure && Hashtbl.mem reachable id && Hashtbl.mem reachable target) then str else "")) edgestr "")^"}\n"



let analyze_termset idx =
  let ts = idx.termbase in
  let scaling = 100 in
  let heavy_sharing = 2 in

  print_string  ( "\n------------- The Termset Analysis -------------"^"\n");
  print_string "Heavily shared nodes:\n";
  let shared = Hashtbl.create 10 in
  let parents id = (if (Hashtbl.mem ts.appl_with_arg id) then (Hashtbl.length (Hashtbl.find ts.appl_with_arg id)) else 0) +
                   (if (Hashtbl.mem ts.appl_with_func id) then (Hashtbl.length (Hashtbl.find ts.appl_with_func id)) else 0) +
                   (if (Hashtbl.mem ts.abstr_with id) then (Hashtbl.length (Hashtbl.find ts.abstr_with id)) else 0)
      in
  let number_of_bindings = ref 0 in
  let max_bindings =ref 0 in
  let number_of_nodes = Darray.da_size ts.nodes in
  let size_of_symbol_pst = ref 0 in
  let size_of_pst = ref 0 in
  let size_of_terms = ref 0 in
  let symbol_size_of_terms = ref 0 in
  let size_of_bound_pst = ref 0 in
  let bound_size_of_terms = ref 0 in
  let number_of_supernodes = ref 0 in
  let symbol_supernodes = ref 0 in
  let nonprimitive_supernodes = ref 0 in
  let size_total = ref 0 in
  let symbol_number = ref 0 in
  let nonprimitive_number = ref 0 in


  Darray.da_iteri
   (fun i _ -> let pa = parents i in
               number_of_bindings := !number_of_bindings + pa;
               if pa > !max_bindings then max_bindings := pa;
               if pa > heavy_sharing then print_string ((string_of_int pa)^" bindings: "^(Term.to_string (retrieve ts i))^
                                                        " (node "^(string_of_int i)^")\n");
               if Hashtbl.mem shared pa
               then Hashtbl.replace shared pa ((Hashtbl.find shared pa)+1)
               else Hashtbl.add shared pa 1;
               let occurs=(List.length (Hashtbl.find_all idx.occurs_in i)) in
               number_of_supernodes := (!number_of_supernodes) + occurs;
               match (get_node ts i).structure with
                 Symbol_node _ -> (symbol_supernodes := (!symbol_supernodes) + occurs;
                                   symbol_number := (!symbol_number) +1)
               | Bound_node _ -> ()
               | _ -> (nonprimitive_supernodes := (!nonprimitive_supernodes) + occurs;
                       nonprimitive_number := (!nonprimitive_number) + 1);
               let sot = size_of_term ts i in
               size_total := (!size_total)+sot;
               Hashtbl.iter
               (fun a b -> size_of_pst := (!size_of_pst) + Position.size_of b;
                           size_of_terms := (!size_of_terms) + sot;
                           match (get_node ts a).structure with
                             Symbol_node _ -> (size_of_symbol_pst := (!size_of_symbol_pst)+ (Position.size_of b);
                                              symbol_size_of_terms := (!symbol_size_of_terms) + sot)
                          |  Bound_node  _ -> ()
                                              (*(size_of_symbol_pst := (!size_of_symbol_pst)+ (Position.size_of b);
                                              symbol_size_of_terms := (!symbol_size_of_terms) + sot)*)
                          |  _ -> ())
               (Hashtbl.find idx.occurrences i);
               if Hashtbl.mem idx.boundvars i
               then List.iter
               (fun a -> (size_of_bound_pst := (!size_of_bound_pst)+ (Position.size_of a);
                          bound_size_of_terms := (!bound_size_of_terms) + sot))
               (Hashtbl.find idx.boundvars i))
   ts.nodes;
  let number_of_bindings = !number_of_bindings in
  let max_bindings = !max_bindings in
  let rec list_of n  = if n <= 0 then [] else (ref 0)::(list_of (n-1)) in
  let stats1 = (list_of scaling) in
  let stats2 = ref [] in
  let stats2ub = ref [0] in
  let stats2lb = ref [0] in
  let stats2n = ref 0 in
  let stats2last = ref 0 in

  let bindings =
    Hashtbl.fold
     (fun a b c -> let x = if max_bindings > 0 then (a*(scaling-1))/max_bindings else (a*(scaling-1)) in
                   (List.nth stats1 x) := !(List.nth stats1 x)+b;
                   (a,b)::c)
      shared [] in


  List.iter
    (fun p -> match p with (a,b) -> (* print_string ((string_of_int b)^" node(s) with "^(string_of_int a)^" bindings\n") ;*)
                                    if a>(List.hd !(stats2lb)) && !stats2n >= (number_of_nodes/scaling) then
                                    (stats2 := ((!stats2n)::!stats2);
                                     stats2n := 0;
                                     stats2ub := (!stats2last::!stats2ub);
                                     stats2lb := (a::!stats2lb));
                                    stats2n := !stats2n + b;
                                    stats2last := a;
                                    )
  (List.sort (fun a b -> match (a,b) with ((v,_),(y,_)) -> if v>y then 1 else if v=y then 0 else (-1)) bindings);

  stats2 := ((!stats2n)::!stats2);
  stats2ub := (!stats2last::!stats2ub);


  let stats2 = (List.rev !stats2) in
  let stats2ub = (List.tl (List.rev !stats2ub)) in
  let stats2lb = (List.rev !stats2lb) in

  let rec show_stats2 r = match r with
                             (a::ar,ub::ubr,lb::lbr) -> (print_string ("From "^(string_of_int lb)^
                                                         " to "^(string_of_int ub)^" bindings: "^
                                                         (string_of_int a)^" node(s)\n");
                                                         show_stats2 (ar,ubr,lbr)) |
                             _ -> ()
  in


  print_string "\nStatistics:\n";
  for i=0 to (scaling-1) do
    let x = !(List.nth stats1 i) in
    if x > 0 then
    print_string ("From "^(string_of_int ((i*max_bindings)/scaling))^" to "^(string_of_int (((i+1)*max_bindings)/scaling))^
                  " bindings: "^(string_of_int x)^" node(s)\n")
  done;
  print_string "\nDetails of dense areas:\n";
  show_stats2 (stats2,stats2ub,stats2lb);

  print_string "\nSharing rate: ";
  print_string ((string_of_int number_of_nodes)^
                " nodes with "^(string_of_int number_of_bindings)^
                " bindings\n"^
                "Average sharing rate:                              "^
               (string_of_float ((float_of_int number_of_bindings)/.(float_of_int number_of_nodes)))^
                " bindings per node\n");
  print_string ("Average term size:                                 "^
               (string_of_float ((float_of_int (!size_total))/.(float_of_int (number_of_nodes))))^"\n");
  print_string ("Average number of supernodes:                      "^
               (string_of_float ((float_of_int (!number_of_supernodes))/.(float_of_int (number_of_nodes))))^"\n");
  print_string ("Average number of supernodes (symbols):            "^
               (string_of_float ((float_of_int (!symbol_supernodes))/.(float_of_int (!symbol_number))))^"\n");
  print_string ("Average number of supernodes (nonprimitive terms): "^
               (string_of_float ((float_of_int (!nonprimitive_supernodes))/.(float_of_int (!nonprimitive_number))))^"\n");
  print_string ("Rate of term occurrences PST size / term size:     "^
               (string_of_float ((float_of_int (!size_of_pst))/.(float_of_int (!size_of_terms))))^"\n");
  print_string ("Rate of symbol occurrences PST size / term size:   "^
               (string_of_float ((float_of_int (!size_of_symbol_pst))/.(float_of_int (!symbol_size_of_terms))))^"\n");
  print_string ("Rate of bound occurrences PST size / term size:    "^
               (string_of_float ((float_of_int (!size_of_bound_pst))/.(float_of_int (!bound_size_of_terms)))));
  print_string  ( "\n------------- End Termset Analysis -------------"^"\n")


(* FIXME part of unused old term-ordering definition. For some changes to that see r1546
         (in particular w1 and w2 were renamed in that revision).
(* w1: typeorder-ordering lifted to terms *)
let w1 ts typeord = function
    Symbol_node s -> (try (typeord (type_of_symbol !signature s)) with Failure _ -> failwith ("type of symbol "^s^" unknown"))
  | Abstr_node(ty,id) ->
      let ty' = node_type ts id in
      (typeord (abstr_type ty ty')) + (typeord ty) + (typeord ty')
  | Appl_node(id1,id2) ->
      let ty1 = node_type ts id1 in
      let ty2 = node_type ts id2 in
      (typeord ty1) + (typeord ty2)
  | Bound_node(ty,_) -> typeord ty


(* w1: symbolweights-ordering lifted to terms *)
let rec w2 ts symbord = function
    Symbol_node s -> (try (symbord s) with _ -> 0)
  | Abstr_node(ty,id) -> w2 ts symbord (get_node ts id).structure
  | Appl_node(id1,id2) -> (w2 ts symbord (get_node ts id1).structure) + (w2 ts symbord (get_node ts id2).structure)
  | Bound_node(ty,_) -> 0

let make_termordering ts typeord symbord id =
  let n = (get_node ts id).structure in
  (w1 ts typeord n,w2 ts symbord n)
*)





let analyze_termset_males idx =
  let ts = idx.termbase in
  let scaling = 100 in
  let shared = Hashtbl.create 10 in
  let parents id = (if (Hashtbl.mem ts.appl_with_arg id) then (Hashtbl.length (Hashtbl.find ts.appl_with_arg id)) else 0) +
                   (if (Hashtbl.mem ts.appl_with_func id) then (Hashtbl.length (Hashtbl.find ts.appl_with_func id)) else 0) +
                   (if (Hashtbl.mem ts.abstr_with id) then (Hashtbl.length (Hashtbl.find ts.abstr_with id)) else 0)
      in
  let number_of_bindings = ref 0 in
  let max_bindings =ref 0 in
  let number_of_nodes = Darray.da_size ts.nodes in
  let size_of_symbol_pst = ref 0 in
  let size_of_pst = ref 0 in
  let size_of_terms = ref 0 in
  let symbol_size_of_terms = ref 0 in
  let size_of_bound_pst = ref 0 in
  let bound_size_of_terms = ref 0 in
  let number_of_supernodes = ref 0 in
  let symbol_supernodes = ref 0 in
  let nonprimitive_supernodes = ref 0 in
  let size_total = ref 0 in
  let symbol_number = ref 0 in
  let nonprimitive_number = ref 0 in

  Darray.da_iteri
   (fun i _ -> let pa = parents i in
               number_of_bindings := !number_of_bindings + pa;
               if pa > !max_bindings then max_bindings := pa;
               if Hashtbl.mem shared pa
               then Hashtbl.replace shared pa ((Hashtbl.find shared pa)+1)
               else Hashtbl.add shared pa 1;
               let occurs=(List.length (Hashtbl.find_all idx.occurs_in i)) in
               number_of_supernodes := (!number_of_supernodes) + occurs;
               match (get_node ts i).structure with
                 Symbol_node _ -> (symbol_supernodes := (!symbol_supernodes) + occurs;
                                   symbol_number := (!symbol_number) +1)
               | Bound_node _ -> ()
               | _ -> (nonprimitive_supernodes := (!nonprimitive_supernodes) + occurs;
                       nonprimitive_number := (!nonprimitive_number) + 1);
               let sot = size_of_term ts i in
               size_total := (!size_total)+sot;
               Hashtbl.iter
               (fun a b -> size_of_pst := (!size_of_pst) + Position.size_of b;
                           size_of_terms := (!size_of_terms) + sot;
                           match (get_node ts a).structure with
                             Symbol_node _ -> (size_of_symbol_pst := (!size_of_symbol_pst)+ (Position.size_of b);
                                              symbol_size_of_terms := (!symbol_size_of_terms) + sot)
                          |  Bound_node  _ -> ()
                                              (*(size_of_symbol_pst := (!size_of_symbol_pst)+ (Position.size_of b);
                                              symbol_size_of_terms := (!symbol_size_of_terms) + sot)*)
                          |  _ -> ())
               (Hashtbl.find idx.occurrences i);
               if Hashtbl.mem idx.boundvars i
               then List.iter
               (fun a -> (size_of_bound_pst := (!size_of_bound_pst)+ (Position.size_of a);
                          bound_size_of_terms := (!bound_size_of_terms) + sot))
               (Hashtbl.find idx.boundvars i))
   ts.nodes;
  let number_of_bindings = !number_of_bindings in
  let max_bindings = !max_bindings in
  let rec list_of n  = if n <= 0 then [] else (ref 0)::(list_of (n-1)) in
  let stats1 = (list_of scaling) in
  let stats2 = ref [] in
  let stats2ub = ref [0] in
  let stats2lb = ref [0] in
  let stats2n = ref 0 in
  let stats2last = ref 0 in

  let bindings =
    Hashtbl.fold
     (fun a b c -> let x = if max_bindings > 0 then (a*(scaling-1))/max_bindings else (a*(scaling-1)) in
                   (List.nth stats1 x) := !(List.nth stats1 x)+b;
                   (a,b)::c)
      shared [] in

  List.iter
    (fun p -> match p with (a,b) -> (* print_string ((string_of_int b)^" node(s) with "^(string_of_int a)^" bindings\n") ;*)
                                    if a>(List.hd !(stats2lb)) && !stats2n >= (number_of_nodes/scaling) then
                                    (stats2 := ((!stats2n)::!stats2);
                                     stats2n := 0;
                                     stats2ub := (!stats2last::!stats2ub);
                                     stats2lb := (a::!stats2lb));
                                    stats2n := !stats2n + b;
                                    stats2last := a;
                                    )
  (List.sort (fun a b -> match (a,b) with ((v,_),(y,_)) -> if v>y then 1 else if v=y then 0 else (-1)) bindings);

  stats2 := ((!stats2n)::!stats2);
  stats2ub := (!stats2last::!stats2ub);

  let rec order = function
      Basetype "$o" -> 1
    | Basetype "'A" -> -1
    | Basetype _ -> 0
    | Funtype (a,b) -> let orda = (order a) and ordb = (order b) in 
	if orda < 0 || ordb < 0 then -1 
	else (max (orda +1) ordb)
  in

  let termbase_maxtype_order =
    let maxord = ref 0 in
    let maxtype = ref "$tType$" in
      Hashtbl.iter 
	(fun _ ty -> 
	   let neword = (order ty) in
	     if neword > !maxord then (maxord := neword; maxtype := (Hol_type.to_string ty)) else ()) 
	idx.termbase.nodetypes;
      (!maxord,!maxtype)
  in

  let rec size = function
    | Basetype _ -> 1
    | Funtype (a,b) -> ((size a) + (size b)) 
  in

  let termbase_maxtype_size =
    let maxsize = ref 0 in
    let maxtype = ref "$tType$" in
      Hashtbl.iter 
	(fun _ ty -> 
	   let newsize = (size ty) in
	     if newsize > !maxsize then (maxsize := newsize; maxtype := (Hol_type.to_string ty)) else ()) 
	idx.termbase.nodetypes;
      (!maxsize,!maxtype)
  in

  let contained_primeqs = (Hashtbl.find_all idx.has_headsymbol (create idx.termbase (Symbol "="))) in
  let contains_primeq = if (List.length contained_primeqs) = 0 then 0 else 1 in
  let no_of_contained_primeqs = (List.length contained_primeqs) in

(**  
  let contained_primeq_types = (List.map (fun id -> type_of idx id) contained_primeqs) in
  
  let primeqs_maxtype_size =
    let maxsize = ref 0 in
    let maxtype = ref "$tType$" in
      List.iter 
	(fun ty -> 
	   let newsize = (size ty) in
	     if newsize > !maxsize then (maxsize := newsize; maxtype := (Hol_type.to_string ty)) else ()) 
	contained_primeq_types;
      (!maxsize,!maxtype)
  in
    
  let primeqs_maxtype_order =
    let maxord = ref 0 in
    let maxtype = ref "$tType$" in
      List.iter 
	(fun ty -> 
	   let neword = (order ty) in
	     if neword > !maxord then (maxord := neword; maxtype := (Hol_type.to_string ty)) else ()) 
	contained_primeq_types;
      (!maxord,!maxtype)
  in
**)

  print_string ((string_of_int number_of_nodes)^" % nodes\n");
  print_string ((string_of_int number_of_bindings)^" % bindings\n");
  print_string ((string_of_float ((float_of_int number_of_bindings)/.(float_of_int number_of_nodes)))^" % average sharing rate (bindings per node)\n");
  print_string ((string_of_float ((float_of_int (!size_total))/.(float_of_int (number_of_nodes))))^" % average term size\n");                   
  print_string ((string_of_float ((float_of_int (!number_of_supernodes))/.(float_of_int (number_of_nodes))))^" % average number of supernodes\n");
  print_string ((string_of_float ((float_of_int (!symbol_supernodes))/.(float_of_int (!symbol_number))))^" % average number of supernodes (symbols)\n");
  let rate0 = if !nonprimitive_number > 0 then ((float_of_int (!nonprimitive_supernodes))/.(float_of_int (!nonprimitive_number))) else 0.0 in
    print_string ((string_of_float rate0)^" % average number of supernodes (nonprimitive terms)\n");
  let rate1 = if !size_of_terms > 0 then ((float_of_int (!size_of_pst))/.(float_of_int (!size_of_terms))) else 0.0 in
    print_string ((string_of_float rate1)^" % rate of term occurrences PST size / term size\n");
  let rate2 = if !symbol_size_of_terms > 0 then ((float_of_int (!size_of_symbol_pst))/.(float_of_int (!symbol_size_of_terms))) else 0.0 in
    print_string ((string_of_float rate2)^" % rate of symbol occurrences PST size / term size\n");
  let rate3 = if !bound_size_of_terms > 0 then ((float_of_int (!size_of_bound_pst))/.(float_of_int (!bound_size_of_terms))) else 0.0 in
    print_string ((string_of_float rate3)^" % rate of bound occurrences PST size / term size\n");
  let (maxord,maxtype) = termbase_maxtype_order in
    print_string ((string_of_int maxord)^" % maximal order of types in termbase; maxtype is: "^maxtype^"\n");
  let (maxsize,maxtype) = termbase_maxtype_size in
    print_string ((string_of_int maxsize)^" % maximal size of types in termbase; maxtype is: "^maxtype^"\n");
  print_string ((string_of_int contains_primeq)^" % contains primitive equality\n");
  print_string ((string_of_int no_of_contained_primeqs)^" % no of subterms with primitive equality symbols\n")
 
