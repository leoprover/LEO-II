
open Hol_type
open Term
open Termset
open Signature


type 'a xterm =
    Explicit of term
  | Indexed of 'a termindex * int

let signature = ref (new_signature ())

let set_signature sigma =
  signature := sigma;
  Termset.set_signature sigma

let get_signature () =
  !signature

let new_termset = Termset.new_termset

let new_index = Termset.new_index

let free_vars = function
    Explicit t -> List.map (fun s -> Symbol s) (Term.free_vars t)
  | Indexed (idx,id) -> if (Hashtbl.mem idx.freevars id)
                        then IdSet.fold (fun id2 l -> (Termset.retrieve idx.Termset.termbase id)::l) (Hashtbl.find idx.freevars id) []
                        else []

let get_head_symbol = function
    Explicit t -> Explicit (get_head_symbol t)
  | Indexed (idx,id) -> Explicit (get_head_symbol (retrieve idx.termbase id))


let term2xterm t = Explicit t

let xterm2term = function
    Explicit t -> t
  | Indexed(idx,id) -> retrieve idx.termbase id

type 'a xintermediate =
    Xsymbol of string * 'a xterm
  | Xappl of 'a xintermediate * 'a xintermediate * 'a xterm
  | Xabstr of 'a xintermediate * hol_type * 'a xintermediate * 'a xterm
  | Xend of 'a xterm

let rec xterm2im t d = 
  if d = 0 then Xend t
  else match t with
    Explicit (Appl (a, b)) -> Xappl ((xterm2im (Explicit a) (d-1)), (xterm2im (Explicit b) (d-1)), t)
  | Explicit (Abstr (a, ty, b)) -> Xabstr ((xterm2im (Explicit a) (d-1)), ty, (xterm2im (Explicit b) (d-1)), t)
  | Explicit (Symbol s) -> Xsymbol (s, t)
  | Indexed (idx,id) ->
    (match (nstruct idx id) with
       Symbol_node s -> Xsymbol (s, t)
     | Appl_node (id1, id2) -> Xappl ((xterm2im (Indexed (idx, id1)) (d-1)),
                                     (xterm2im (Indexed (idx, id2)) (d-1)),
                                     t)
     | Abstr_node (ty, id1) -> Xabstr (Xsymbol ("0",Indexed (idx,(insert_and_index idx (Bound_node(ty,0))))),
                                       ty,
                                       (xterm2im (Indexed (idx, id1)) (d-1)), t)
     | Bound_node (ty, i) -> Xsymbol ((string_of_int i), t)
    )

let im2xterm = function
    Xsymbol(_,t) -> t
  | Xappl(_,_,t) -> t
  | Xabstr(_,_,_,t) -> t
  | Xend t -> t

let im2term t = xterm2term (im2xterm t)

let mk_var s =
  Explicit(Symbol s)

let mk_const s =
  (* assert(Signature.is_defined_symbol !signature  s or Signature.is_uninterpreted_symbol !signature s); *)
  Explicit(Symbol s)

let mk_abs tvar htype tbody =
  match (tvar,tbody) with
     (Explicit ttvar, Explicit ttbody) ->
       Explicit(Abstr(ttvar,htype,ttbody))
   | (Indexed(idx,_),Explicit ttbody) ->
       let idbody = index_term ttbody idx in
       let idabs = insert_and_index idx (Abstr_node(htype,idbody)) in
       Indexed(idx,idabs)
   | (Explicit _, Indexed(idx,idbody)) ->
       let idabs = insert_and_index idx (Abstr_node(htype,idbody)) in
       Indexed(idx,idabs)
   | (Indexed(idx,_),Indexed(idx',idbody)) ->
       if idx=idx' then
         let idabs = insert_and_index idx (Abstr_node(htype,idbody)) in
         Indexed(idx,idabs)
       else failwith "mk_abs: indices do not match"


let mk_appl t1 t2 =
  match (t1,t2) with
      (Explicit tt1,Explicit tt2) ->
        Explicit(Appl(tt1,tt2))
    | (Indexed(idx,idt1),Explicit tt2) ->
        let idt2 = index_term tt2 idx in
	let idappl = insert_and_index idx (Appl_node(idt1,idt2)) in
	Indexed(idx,idappl)
    | (Explicit tt1,Indexed(idx,idt2)) ->
        let idt1 = index_term tt1 idx in
	let idappl = insert_and_index idx (Appl_node(idt1,idt2)) in
	Indexed(idx,idappl)
   | (Indexed(idx,idt1),Indexed(idx',idt2)) ->
        if idx=idx' then
	  let idappl = insert_and_index idx (Appl_node(idt1,idt2)) in
	  Indexed(idx,idappl)
	else failwith "mk_appl: indices do not match"


let is_symbol = function
    Explicit t -> Term.is_symbol t
  | Indexed(idx,id) -> 
      match (get_node idx.termbase id).structure with
          Symbol_node _ -> true
        | _ -> false


let is_variable = function
    Explicit t -> Term.is_variable t
  | Indexed(idx,id) ->
      match (get_node idx.termbase id).structure with
          Symbol_node s -> Term.is_variable (Symbol s)
	| _ -> false


let is_constant t = (is_symbol t) && (not (is_variable t))
    

let is_appl = function
    Explicit t -> Term.is_appl t
  | Indexed(idx,id) -> 
      match (get_node idx.termbase id).structure with
          Appl_node _ -> true
	| _ -> false


let is_abstr = function
    Explicit t -> Term.is_abstr t
  | Indexed(idx,id) -> 
      match (get_node idx.termbase id).structure with
          Abstr_node _ -> true
	| _ -> false


let dest_symbol = function
    Explicit t -> Term.get_symbol t
  | Indexed(idx,id) ->
      match (get_node idx.termbase id).structure with
          Symbol_node s -> s
	| _ -> failwith "Termsystem.dest_symbol: not a symbol"


let dest_appl = function
    Explicit t -> (
      match t with
          Appl(t1,t2) -> (Explicit t1, Explicit t2)
	| _ -> failwith "Termsystem.dest_appl: not an application")
  | Indexed(idx,id) ->
      match (get_node idx.termbase id).structure with
          Appl_node(id1,id2) -> (Indexed(idx,id1),Indexed(idx,id2))
	| _ -> failwith "Termsystem.dest_appl: not an application"


let dest_abstr = function
    Explicit t -> (
      match t with
          Abstr(x,ty,t1) -> (get_symbol x,ty,Explicit t1)
	| _ -> failwith "Termsystem.dest_abstr: not an abstraction")
  | Indexed(idx,id) ->
      match (get_node idx.termbase id).structure with
          Abstr_node(ty,id1) -> ("db",ty,Indexed(idx,id1))
	| _ -> failwith "Termsystem.dest_abstr: not an abstraction"


let free_variables = function
    Explicit t -> Term.free_vars t
  | Indexed(idx,id) -> failwith "not implemented yet"


let is_indexed = function
    Explicit _ -> false
  | Indexed _  -> true

let index idx = function
    Explicit t -> Indexed(idx, Termset.index_term t idx)
  | Indexed(idx',id) ->
      if idx=idx' then
        Indexed(idx,id)
      else (* Do we want this? *)
        let t = Termset.retrieve idx'.Termset.termbase id in
	Indexed(idx, Termset.index_term t idx)

let index_with_role idx t r = match t with
    Explicit t -> Indexed(idx, Termset.index_with_role idx t r)
  | Indexed(idx',id) ->
      if idx=idx' then
        (Termset.set_role idx id r;
         Indexed(idx,id))
      else (* Do we want this? *)
        let t = Termset.retrieve idx'.Termset.termbase id in
	Indexed(idx, Termset.index_with_role idx t r)

let unindex_role idx r = unset_role idx r

let clear_role_index idx = Termset.clear_role_index idx


let unindex = function
    Explicit _ -> ()
  | Indexed(idx,id) ->
      Termset.unindex_node id idx;
      Termset.remove_node idx.termbase id

let type_of = function
    Explicit t -> Term.type_of (type_of_symbol !signature) t
  | Indexed(idx,id) -> node_type idx.termbase id

let to_string = function
    Explicit t -> Term.to_string t
  | Indexed(idx,id) -> Term.to_string (Termset.retrieve idx.termbase id)


let to_hotptp = function
    Explicit t -> Term.to_hotptp t
  | Indexed(idx,id) -> Term.to_hotptp (Termset.retrieve idx.termbase id)

let to_post = function
    Explicit t -> Term.to_post t
  | Indexed(idx,id) -> Term.to_post (Termset.retrieve idx.termbase id)

let get_id idx = function
    Explicit t -> Termset.index_term t idx
  | Indexed(idx',id) ->
      if idx=idx' then
        id
      else (* Do we want this? *)
        let t = Termset.retrieve idx'.Termset.termbase id in
	Termset.index_term t idx


let occurs_in idx t1 t2 =
  let id1 = get_id idx t1 in
  if (Hashtbl.mem idx.occurrences (get_id idx t1)) then
  (let oc=Hashtbl.find idx.occurrences id1 in
     Hashtbl.mem oc (get_id idx t2))
  else false

let substitute idx t s =  
  let t' = get_id idx t in
  let s' = List.map (fun (a,b) -> (get_id idx a, get_id idx b)) s in
  Indexed (idx,Substitution.apply_subst idx s' t')

