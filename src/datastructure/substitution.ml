(* ========================================================================= *)
(* Substitutions                                                             *)
(* ========================================================================= *)

(** Module Substitution implements substitutions and their application.
    @author Frank
    @since 31-08-06*)

open Hol_type
open Term
open Signature
open Termset
open Position

type replacement = id positiontable

type substitution = (id*id) list

let rec apply_replace ts id rplc =
match (rplc,(Termset.get_node ts id).structure) with
  (Empty,_) -> id |
  (Table(Empty,Empty,Empty, WithData d),_) -> d |
  (Table(a,b,c,WithData d),_) -> (apply_replace ts d (Table(a,b,c,NoData))) |
  (Table(Empty,a,b,NoData),Appl_node(a1,b1)) -> Termset.insert ts (Appl_node((apply_replace ts a1 a),(apply_replace ts b1 b))) |
  (Table(a,Empty,Empty,NoData),Abstr_node(t,b)) -> Termset.insert ts (Abstr_node(t,(apply_replace ts b a))) |
  (_,_) -> raise Not_found

let rec replace_by_fun ts id rplc f =
match (rplc,(Termset.get_node ts id).structure) with
  (Empty,_) -> id |
  (Table(Empty,Empty,Empty, WithData d),_) -> (f d id) |
  (Table(a,b,c,WithData d),_) -> (replace_by_fun ts (f d id) (Table(a,b,c,NoData)) f) |
  (Table(Empty,a,b,NoData),Appl_node(a1,b1)) -> Termset.insert ts (Appl_node((replace_by_fun ts a1 a f),(replace_by_fun ts b1 b f))) |
  (Table(a,Empty,Empty,NoData),Abstr_node(t,b)) -> Termset.insert ts (Abstr_node(t,(replace_by_fun ts b a f))) |
  (_,_) -> raise Not_found



let rec next_data l =
  match l with
    (f,Table(_,_,_,WithData d))::_ -> WithData (f, d)
  | (_,Table(_,_,_,NoData))::r -> next_data r
  | (_,Empty)::r -> next_data r
  | [] -> NoData

let rec next_func l =
  match l with
    (_,Table(_,Empty,_,_))::r -> next_func r
  | (f,Table(_,t,_,_))::r -> (f,t)::next_func r
  | (_,Empty)::r -> next_func r
  | [] -> []

let rec next_arg l =
  match l with
    (_,Table(_,_,Empty,_))::r -> next_arg r
  | (f,Table(_,_,t,_))::r -> (f,t)::next_arg r
  | (_,Empty)::r -> next_arg r
  | [] -> []

let rec next_abstr l =
  match l with
    (_,Table(Empty,_,_,_))::r -> next_abstr r
  | (f,Table(t,_,_,_))::r -> (f,t)::next_abstr r
  | (_,Empty)::r -> next_abstr r
  | [] -> []


type 'c env = Env of (('c env -> Termset.id -> Termset.id) * 'c Position.positiontable) list
                     * (('c env -> Termset.id -> Termset.id) * Hol_type.hol_type) list 
                     * int * int * int

(*
  let rec subst_occs idx s t =
  List.rev (List.map (fun (a,b) ->  ((fun (Env _) -> b),(occurrences t a idx))) s)
*)

let boundvarshift idx t num offset =
  let rec cut l count =
    match l with
      [] -> []
    | hd::tl -> if count < (1 - offset) then ((fun _ -> 1),hd)::(cut l (count+1)) else []
  in
  let bound = if (Hashtbl.mem idx.boundvars t)
              then cut (Hashtbl.find idx.boundvars t) (Hashtbl.find idx.boundoffset t)
              else [] in
  let rec recurse t shifts =
    match (nstruct idx t, shifts) with
      _,[] -> t
    | Appl_node(id1,id2),_ -> insert idx.termbase (Appl_node(recurse id1 (next_func shifts),recurse id2 (next_arg shifts)))
    | Abstr_node(ty,id1),_ -> insert idx.termbase (Abstr_node(ty,recurse id1 (next_abstr shifts)))
    | Bound_node(ty,i),_ -> insert idx.termbase (Bound_node(ty,i+num))
    | _,_ -> t
  in
  recurse t bound


let typed_copy idx a b ty1 env =
(*  let ns = function
      Symbol_node s -> "symbol "^s
    | Appl_node (id1,id2) -> "appl("^(string_of_int id1)^","^(string_of_int id2)^")"
    | Abstr_node (ty,id) -> "abstr("^(Hol_type.to_hotptp ty)^","^(string_of_int id)^")"
    | Bound_node (ty,idx) -> "bound("^(Hol_type.to_hotptp ty)^","^(string_of_int idx)^")"
  in
  Util.sysout 3 "generate typed copy for:\n";
  Util.sysout 3 ((ns (nstruct idx a))^"\n");*)
  match env with
    Env (occs,args,scope,shift,offset) -> 
  match (nstruct idx a),args with
    (Symbol_node "?",(_,Funtype (ty2,_))::_) ->
    (*Util.sysout 3 "... for exists\n";*)
    index_term
    (Abstr(Symbol "P",abstr_type ty2 bt_o,
      Appl(Symbol neg,Appl(Symbol forall,
        Abstr(Symbol "X",ty2,
          Appl(Symbol neg,Appl(Symbol "P",Symbol "X")))))))
    idx
  | _ -> (*Util.sysout 3 "... for anything\n"; *)
         b


(* let mv = ref ""*)

let rec insert_arg_f idx s t env1 env2 t2 =
(*  Util.sysout 3 ((!mv)^"Insert-Arg-Function\n");*)
  match (env1,env2) with
    (Env (occs1,args1,scope1,shift1,offset1),Env (occs2,args2,scope2,shift2,offset2)) ->
      apply_subst' idx s t occs1 args2 scope2 (shift1 + (scope2-scope1)) offset1

and subst_repl_f idx s a b env t =
  let b' = typed_copy idx a b (Termset.type_of idx t) env in
  match env with
    Env (occs,args,scope,shift,offset) -> apply_subst' idx s b' (subst_occs idx s b') args scope shift offset

and shift_bound_f idx s shift1 env t =
  match env,(nstruct idx t) with
    Env (occs,args,scope,shift2,offset),Bound_node(ty,i) -> 
      rebuild_appl idx s (insert idx.termbase (Bound_node(ty,((i+shift2)-shift1)))) args (Env ([],args,scope,shift2,offset))
  | _ -> t

and subst_occs idx s t =
(*  Util.sysout 3 ((!mv)^"subst_occ: "^(Term.to_string (Termset.retrieve idx.termbase t))^"\n");*)
  List.rev (List.map (fun (a,b) ->  ((subst_repl_f idx s a b),(occurrences t a idx))) s)

and rebuild_appl idx s t args env =
(*  Util.sysout 3 ((!mv)^"rebuild appl\n");*)
  match args,env with
    [],_  -> t
  | (argf,_)::r,Env (occs,_,scope,shift,offset) -> 
      rebuild_appl idx s (insert idx.termbase (Appl_node(t,(argf (Env (occs,[],scope,shift,offset)) t)))) r (Env (occs,r,scope,shift,offset))
(*  | _,_ -> t *)

and apply_subst' idx s t occs args scope shift offset =
(*  Util.sysout 3 ((!mv)^"subst: "^(Term.to_string (Termset.retrieve idx.termbase t))^"\n");
  Util.sysout 3 ((!mv)^"  args: "^(string_of_int (List.length args)));
  Util.sysout 3 (", scope: "^(string_of_int scope));
  Util.sysout 3 (", shift: "^(string_of_int shift)^"\n");
  let mv_old=(!mv) in
  mv:="|"^(!mv);*)
(*  Util.sysout 3 ("subst': "^(Term.to_string (Termset.retrieve idx.termbase t))^"\n");
  List.iter (fun (a,b) -> Util.sysout 3 ((Term.to_string (Termset.retrieve idx.termbase a))^"/"^(Term.to_string (Termset.retrieve idx.termbase b))^",\n"))
            s;
  Util.sysout 3 "]\n";*)
  let occs = List.filter (fun a -> match a with (_,Empty) -> false | _ -> true) occs in
(*  Util.sysout 3 "occs...";*)
  let nodestruct = nstruct idx t in
(*  Util.sysout 3 "struct...";*)
  let t_new =
  match (nodestruct,occs,args) with 
    (_,[],[]) -> boundvarshift idx t shift offset
  | (Appl_node(_,_),[],_) -> rebuild_appl idx s (boundvarshift idx t shift offset) args (Env (occs,args,scope,shift,offset))
  | (_,_,_) ->
  match (next_data occs) with
    WithData (f,d) -> (*Util.sysout 3 ((!mv)^"replace\n");*)
                      f (Env (occs, args, scope, shift, offset)) t
  | NoData ->
  match nodestruct with
    Symbol_node _      -> rebuild_appl idx s t args (Env (occs,args,scope,shift,offset))
  | Bound_node (ty,i)  -> rebuild_appl idx s (insert idx.termbase (Bound_node(ty,i+shift))) args (Env (occs,args,scope,shift,offset))
  | Abstr_node (ty,t1) ->
      (match args with
        []     -> insert idx.termbase (Abstr_node(ty,
                  apply_subst' idx s t1 (((shift_bound_f idx s shift),(beta_reducable t1 idx))::(next_abstr occs)) [] (scope+1) shift offset))
      | (a1,ty1)::ar -> apply_subst' idx s t1 ((a1,(beta_reducable t1 idx))::(next_abstr occs)) ar scope (shift - 1) offset)
  | Appl_node (t1,t2) ->  (*Util.sysout 3 ((!mv)^"new_arg: "^(Term.to_string (Termset.retrieve idx.termbase t2))^"\n");*)
                          apply_subst' idx s t1 (next_func occs)
                          (((insert_arg_f idx s t2 (Env((next_arg occs),[],scope,shift,offset))),(Termset.type_of idx t2))::args)
                          scope shift offset
  in
(*  mv:=mv_old;
  Util.sysout 3 ((!mv)^"ret:   "^(Term.to_string (Termset.retrieve idx.termbase t_new))^"\n");
  Util.sysout 3 ((!mv)^"  from: "^(Term.to_string (Termset.retrieve idx.termbase t))^"\n");
  Util.sysout 3 ((!mv)^"  args: "^(string_of_int (List.length args)));
  Util.sysout 3 (", scope: "^(string_of_int scope));
  Util.sysout 3 (", shift: "^(string_of_int shift)^"\n");*)
  index_node t_new idx;
(*  Util.sysout 3 "indexed\n";
  Util.sysout 3 ("    --> "^(Term.to_string (Termset.retrieve idx.termbase t))^"\n[\n");*)
  t_new




let apply_subst idx s t =
  try
  let occs = subst_occs idx s t in
  apply_subst' idx s t occs [] 0 0 0
  with e -> Util.sysout 3 ((Printexc.to_string e)^"\n");
  Util.sysout 3 ("subst: "^(Term.to_string (Termset.retrieve idx.termbase t))^"\n[\n");
  List.iter (fun (a,b) -> Util.sysout 3 ((Term.to_string (Termset.retrieve idx.termbase a))^"/"^(Term.to_string (Termset.retrieve idx.termbase b))^",\n"))
            s;
  Util.sysout 3 "]\n";
  raise (Failure "apply_subst")

let normalize_appl idx t1 t2 =
  apply_subst' idx [] t1 [] [] 0 0 0
