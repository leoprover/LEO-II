(* ========================================================================= *)
(* Calculus                                                                  *)
(* ========================================================================= *)

(** Module Calculus implements the calculus rules for LEO-II
    -- Strongly Preliminary Version --
    @author Chris
    @since 30-11-06*)

open Util
open Hol_type
open Position
open Term
open Termset
open Termsystem
open Signature
open Literal
open Clause
open Clauseset
open State
open Main
open General

exception Calculus_failure of string
exception Literal_not_found


let rec get_head (t:role xterm) =
  match (xterm2im t 1) with 
    Xsymbol(s1,ty1) -> im2xterm (Xsymbol(s1,ty1))
  | Xappl(t1,t2,_) -> get_head (im2xterm t1)
  | Xabstr(_,_,body,_) -> get_head (im2xterm body)  
  | _ -> raise (Failure "get_head in pre_unify")
	
	
let rec get_args (t:role xterm) =
  match (xterm2im t 1) with 
    Xsymbol(s1,_) -> []
  | Xappl(t1,t2,_) -> ((get_args (im2xterm t1))@[im2xterm t2])
  | Xabstr(_,_,_,_) -> []
  | _ -> raise (Failure "get_args in pre_unify")
	


(** Classification of Literals *)

let classify_role st r =
  match r with
      (cln,_,_,pol) -> pol^
        (try
           let cl_unit = Array.length (cl_litarray (find_clause_by_number st cln)) in
             if cl_unit = 1 then "_unit" else "_non_unit"
         with _ -> "_undefined")
        
let get_classifieds st use_lits =
  let classifieds = ref IdSet.empty in
    Hashtbl.iter (fun id role -> if List.mem (classify_role st role) use_lits
                  then classifieds := IdSet.add id (!classifieds))
      st.index.role;
    !classifieds
      
(** Simplify Global *)
      
let rec fixpoints st id pos = 
  match nstruct st.index id with
      Appl_node (id1,id2) ->
	(match ((fixpoints st id1 (List.append pos [Function])),
		(fixpoints st id2 (List.append pos [Arg]))) with 
             ((v1,f1),(v2,f2)) -> if (v1 = "fix" && v2 = "fix")
             then ("fix",[(id,pos)])
             else ("var",List.append f1 f2))
    | Abstr_node (_,id1) -> fixpoints st id1 (List.append pos [Abstraction])
    | Symbol_node s -> if Term.is_variable (Symbol s) then ("var",[]) else ("fix",[(id,pos)])
    | Bound_node _ -> ("fix",[(id,pos)])
	
let rec varpoints st id pos = 
  match nstruct st.index id with
      Appl_node (id1,id2) ->
	(let vars_id1 = varpoints st id1 (List.append pos [Function]) in
	 let vars_id2 = varpoints st id2 (List.append pos [Arg]) in
	   Hashtbl.iter
             (fun v poslist ->
		if Hashtbl.mem vars_id1 v
		then Hashtbl.replace vars_id1 v ((Hashtbl.find vars_id1 v)@poslist)
		else Hashtbl.add vars_id1 v poslist)
	     vars_id2;
	   vars_id1) 
    | Abstr_node (_,id1) -> varpoints st id1 (List.append pos [Abstraction])
    | Symbol_node s -> (let vars = Hashtbl.create 1 in
			  if Term.is_variable (Symbol s) then Hashtbl.add vars id [pos];
			  vars)
    | Bound_node _ -> Hashtbl.create 0
	
	
let lit_subsumes st id =
  let (_,fixp) = fixpoints st id [] in
  let subsumed = ref (match fixp with 
                        (id,pos)::tl -> (try (Hashtbl.find (Hashtbl.find st.index.term_at_pos_role pos) id)
                                   with Not_found -> IdSet.empty)
                      | _ -> IdSet.empty) in
  List.iter (fun (id, pos) -> subsumed := IdSet.inter
                                            (try (Hashtbl.find (Hashtbl.find st.index.term_at_pos_role pos) id)
                                             with Not_found -> IdSet.empty)
                                            (!subsumed))
            fixp;
  IdSet.remove id (!subsumed)

let simplify_global st =
  let idx = st.index in
  let eq = insert idx.termbase (Symbol_node "=") in
  let allequations = try (Hashtbl.find (Hashtbl.find idx.term_at_pos_role [Function;Function]) eq)
                     with Not_found -> IdSet.empty in
  let disposable = ref IdSet.empty in
  IdSet.iter (fun id -> List.iter
                          (fun r -> match r with
                             (cln,pos,_,"pos") -> if (term_at_pos idx id [Function;Arg]) = (term_at_pos idx id [Arg])
                                                then disposable := IdSet.add id (!disposable)
                           | _ -> ())
                        (Hashtbl.find_all idx.role id))
       allequations;
  IdSet.iter (fun id -> Util.sysout 3 ("Equation "^(string_of_int id)^" is disposable.\n")) (!disposable);
  Hashtbl.iter
    (fun _ idset ->
     IdSet.iter
       (fun id ->
        let subsumed = lit_subsumes st id in
        if not (IdSet.is_empty subsumed) then 
         (let clns = List.map (fun (cln,_,_,_) -> cln) (Hashtbl.find_all st.index.role id) in
          Util.sysout 3 ("Term "^(string_of_int id)^":"^(term_to_hotptp st.index.termbase id)^"("^
            (List.fold_left (fun a b -> a^" "^(classify_role st b)) "" (Hashtbl.find_all st.index.role id))
             ^") subsumes:\n");
          IdSet.iter (fun id -> let same = ref false in
                                let other = ref false in
                                List.iter
                                  (fun (cln,_,_,_) -> if List.mem cln clns then same := true else other := true)
                                  (Hashtbl.find_all st.index.role id);
                                let clpos = (if (!same) then "same" else "")^
                                            (if (!same) && (!other) then "/" else "")^
                                            (if (!other) then "other" else "") in
                                Util.sysout 3 ("  term "^(string_of_int id)^":"^(term_to_hotptp st.index.termbase id)^" ("^clpos^" clause)\n")) subsumed))
       idset)    
    (Hashtbl.find idx.term_at_pos_role []);
  []
   
 


(** Exhaustive Definition Unfolding *)

let fold_node_info st id =
  let equals = IdSet.remove id (find_equals st.index id (classify_role st)  ["pos_unit"]) in
  let subst = IdSet.fold (fun id1 l -> (id1,id)::l) equals [] in
  let todo = ref IdSet.empty in
  List.iter (fun (def_id,_) -> if (Hashtbl.mem st.index.occurs_in_role def_id) then
                               todo := IdSet.union (!todo) (Hashtbl.find st.index.occurs_in_role def_id)) subst;
  let replace=Hashtbl.create st.clause_count in
  IdSet.iter (fun id -> let rplc_id = Substitution.apply_subst st.index subst id in
                        (* Util.sysout 3 "Returned from Substitution\n";
                        Util.sysout 3 ("node: "^(Term.to_string (Termset.retrieve (st.index).termbase rplc_id))^"\n"); *)
                        List.iter (fun (cln,b,c,d) ->
                                     let lst=if (Hashtbl.mem replace cln)
                                             then ((cln,b,c,d),Indexed(st.index,id),Indexed(st.index,rplc_id))::(Hashtbl.find replace cln)
                                                  else [((cln,b,c,d),Indexed(st.index,id),Indexed(st.index,rplc_id))] in
                                     Hashtbl.replace replace cln lst)
                         (Hashtbl.find_all st.index.role id))
  (!todo);
(*  Util.sysout 3 "Returned from Indexing\n";*)
  Hashtbl.fold (fun cln lst all -> (cln,lst)::all) replace []

let fold_node_exhaustively st id = 
  let info_list = fold_node_info st id in
  let (oldroles,oldclauses,newclauses) =
    (List.fold_right
       (fun (clnum,role_list) (old_roles,old_clauses,new_clauses) -> 
  Util.sysout 3 ("replacing clause "^(string_of_int clnum)^"\n");
        try
	 let clause = find_and_remove_clause_by_number st clnum in
	 let litarray = Array.copy clause.cl_litarray and
	     pure_roles = ref [] in
	 let (roles,newlits) =
	   let _ = 
	     List.map 
	       (fun ((num,pos,maxflag,pol),_,xterm2) -> 
                 (* !pure_roles <- (num,pos,maxflag,pol)::!pure_roles; *)
                 pure_roles := (num,pos,maxflag,pol)::!pure_roles;
		 litarray.(pos) <-  
		   match pol with
		     "pos" -> lit_mk_pos_literal st.signature xterm2
		   | "neg" -> lit_mk_neg_literal st.signature xterm2
		   | _ -> raise (Failure "fold_node"))
	       role_list in
	   (!pure_roles,(Array.to_list litarray)) 
	 in
	 (* Util.sysout 3 (lit_litlist_to_protocol newlits); *)
	 let newclause = 
	   mk_clause newlits (inc_clause_count st) clause.cl_free_vars 
	     ("rewrite=",[(clause.cl_number,"")],"") clause.cl_origin st in
	 (roles@old_roles,clause::old_clauses,newclause::new_clauses)
        with Failure s  -> (Util.sysout 3 ("Failure: "^s^"\n");(old_roles,old_clauses,new_clauses)))
       info_list ([],[],[])) in
  (oldroles,oldclauses,newclauses)



let unfold_def_info st =
  let subst=List.map
            (fun (def_sym,(def,_)) -> (* (Util.sysout 3 (def_sym^":="^(Term.to_string def)^"\n");*)
                                      (Termset.index_term (Symbol def_sym) st.index,Termset.index_term def st.index))
            (all_defined_symbols st.signature)
  in
  let todo = ref IdSet.empty in
  List.iter (fun (def_id,_) -> if (Hashtbl.mem st.index.occurs_in_role def_id) then
                               todo := IdSet.union (!todo) (Hashtbl.find st.index.occurs_in_role def_id)) subst;
(*  
  let replace= IdSet.fold (fun id rplc -> let rplc_id = Substitution.apply_subst st.index subst id in
                                        (List.map (fun r ->(r,Indexed(st.index,id),Indexed(st.index,rplc_id)))
                                         (Hashtbl.find_all st.index.role id))@rplc)
               (!todo) [] in
  List.map (fun (role,id1,id2) -> (Util.sysout 3 ("\n info:"^(role_to_string role)^" "^(to_string id1)^" "^(to_string id2))))
           replace; 
*)
  let replace=Hashtbl.create st.clause_count in
  IdSet.iter (fun id -> let rplc_id = Substitution.apply_subst st.index subst id in
                        (* Util.sysout 3 "Returned from Substitution\n";
                        Util.sysout 3 ("node: "^(Term.to_string (Termset.retrieve (st.index).termbase rplc_id))^"\n"); *)
                        List.iter (fun (cln,b,c,d) ->
                                     let lst=if (Hashtbl.mem replace cln)
                                             then ((cln,b,c,d),Indexed(st.index,id),Indexed(st.index,rplc_id))::(Hashtbl.find replace cln)
                                                  else [((cln,b,c,d),Indexed(st.index,id),Indexed(st.index,rplc_id))] in
                                     Hashtbl.replace replace cln lst)
                         (Hashtbl.find_all st.index.role id))
  (!todo);
(*  Util.sysout 3 "Returned from Indexing\n";*)
  Hashtbl.fold (fun cln lst all -> (cln,lst)::all) replace []


let rec print_info_list info_list =
    let rec print_role_list role_list =
       match role_list with 
         [] -> "---\n"
       | ((num,pos,maxflag,pol),xterm1,xterm2)::rl ->  "  num: "^(string_of_int num)^" pos: "^(string_of_int pos)^" maxflag: "^maxflag^" pol: "^pol^" xterm1: "^(to_string xterm1)^" xterm2: "^(to_string xterm2)^"\n"^(print_role_list rl)
    in
    match info_list with
       [] -> Util.sysout 1 "------\n"
     | (clnum,role_list)::rl -> (Util.sysout 1 ("\n clnum: "^(string_of_int clnum)^(print_role_list role_list)); print_info_list rl)


let unfold_defs_exhaustively st = 
(*  Util.sysout 3 "\n\n\nEnter \n\n\n"; *)
  let info_list =  unfold_def_info st in
  (* print_info_list info_list; *)
  let (oldroles,oldclauses,newclauses) =
    (List.fold_right
       (fun (clnum,role_list) (old_roles,old_clauses,new_clauses) -> 
	 let clause = find_and_remove_clause_by_number st clnum in
	 let litarray = Array.copy clause.cl_litarray and
	     pure_roles = ref [] in
	 let (roles,newlits) =
	   let _ = 
	     List.map 
	       (fun ((num,pos,maxflag,pol),_,xterm2) -> 
		 (* !pure_roles <- (num,pos,maxflag,pol)::!pure_roles; *)
		 pure_roles := (num,pos,maxflag,pol)::!pure_roles;
		 litarray.(pos) <-  
		   match pol with
		     "pos" -> lit_mk_pos_literal st.signature (term2xterm (ground_poly_syms (xterm2term xterm2) st))
		   | "neg" -> lit_mk_neg_literal st.signature (term2xterm (ground_poly_syms (xterm2term xterm2) st))
		   | _ -> raise (Failure "unfold_def"))
	       role_list in
	   (!pure_roles,(Array.to_list litarray)) 
	 in
	 (* Util.sysout 3 (lit_litlist_to_protocol newlits); *)
	 let newclause = 
	   mk_clause newlits (inc_clause_count st) clause.cl_free_vars 
	     ("unfold_def",[(clause.cl_number,"")],"") clause.cl_origin st in
	 (roles@old_roles,clause::old_clauses,newclause::new_clauses))
       info_list ([],[],[])) in
(*    Util.sysout 3 "\n\n\nLeave \n\n\n"; *)
    (oldroles,oldclauses,newclauses)

  

(** Clause Normalisation *)

let eta_expand1 (t:term) (st:state) =
  match t with 
      Symbol _ ->
	let ty = arg_type (Term.type_of (type_of_symbol st.signature) t) in
	let newvar = create_and_insert_new_free_var (Symbol "Y") ty st in
	  Abstr(newvar,ty,Appl(t,newvar))
    | Appl(_,_) ->  
	let ty = arg_type (Term.type_of (type_of_symbol st.signature) t) in
	let newvar = create_and_insert_new_free_var (Symbol "Y") ty st in
	  Abstr(newvar,ty,Appl(t,newvar))
    | Abstr(x,ty,t) -> Abstr(x,ty,t)


let free_var_term (t:term) (st:state) =
  match (eta_expand1 t st) with 
      Abstr(x,ty,t) -> 
	let nvar = create_and_insert_new_free_var x ty st in 
	  ((beta_normalize (Appl(Abstr(x,ty,t),nvar))),nvar)
    | _ -> raise (Calculus_failure "Free var term failure")   
	
let skolem_term (t:term) (st:state) (free_vars:term list) =
    match (eta_expand1 t st) with 
	Abstr(x,ty,t) -> 
	  let fv_type_list = List.map (fun v -> type_of_symbol st.signature (get_symbol v)) free_vars in
	  let sk_const_ty = List.fold_right (fun t1 t2 -> abstr_type t1 t2) fv_type_list ty in
	  let skoconst = create_and_insert_skolem_const x sk_const_ty st in
	  let skoterm =  List.fold_left (fun t1 t2 -> Appl(t1,t2)) skoconst free_vars in
	    beta_normalize (Appl(Abstr(x,ty,t),skoterm))
      | _ -> raise (Calculus_failure "Skolem term failure")   


let ext_rewrite_equation l1 l2 st = 
  let ty = type_of (im2xterm l1) in
    if ty = Signature.bt_i then raise (Failure "normalize_lit")
    else if ty = Signature.bt_o then
      let t1 = (im2term l1) and t2 = (im2term l2) in
      let negt1 = Appl(Symbol "~",t1) and negt2 = Appl(Symbol "~",t2) in
      let disj1 = Appl(Appl(Symbol "|",t1),t2) and disj2 = Appl(Appl(Symbol "|",negt1),negt2) in
      let negdisj1 = Appl(Symbol "~",disj1) and negdisj2 = Appl(Symbol "~",disj2) in
      let resterm = Appl(Appl(Symbol "|",negdisj1),negdisj2) in
      (term2xterm resterm)
    else if Hol_type.is_funtype ty then
      let (dt, ct) = (arg_type ty, result_type ty) in
      let newvar = create_and_insert_new_free_var (Symbol "X") dt st in
      let nt1 = (beta_normalize (Appl((im2term l1),newvar))) 
      and nt2 = (beta_normalize (Appl((im2term l2),newvar))) in
      let nt = Appl(Symbol "!",Abstr(newvar,dt,Appl(Appl(Symbol "=",nt1),nt2))) in
      (term2xterm nt)
    else raise (Failure "normalize_lit")

let sNeg t = (Appl(Symbol "~",t))

let sOr t1 t2 = (Appl(Appl(Symbol "|",t1),t2)) 

let sAnd t1 t2 = (sNeg (sOr (sNeg t1) (sNeg t2))) 

let sAll var ty t = (Appl(Symbol "!",Abstr(var,ty,t))) 

let special_instantiation_o (nvar:role xterm) (term:role xterm) st flag = 
    let (binding1,binding2) = ([(nvar,(term2xterm  (Symbol ctrue)))],[(nvar,(term2xterm  (Symbol cfalse)))]) in		
    let term1 = (xterm2term (substitute st.index term binding1)) in
    let term2 = (xterm2term (substitute st.index term binding2)) in 
    if flag 
    then [(term2xterm term1); (term2xterm term2)]
    else [(term2xterm (sOr term1 term2))]

let special_instantiation_o_o (nvar:role xterm) (term:role xterm) st flag = 
   let var = create_and_insert_new_free_var (Symbol "X") Signature.bt_o st in
   let binding1 = [(nvar,(term2xterm  (Abstr(var, Signature.bt_o,(Symbol ctrue)))))] and
       binding2 = [(nvar,(term2xterm  (Abstr(var, Signature.bt_o,(Symbol cfalse)))))] and
       binding3 = [(nvar,(term2xterm  (Abstr(var, Signature.bt_o,var))))] and
       binding4 = [(nvar,(term2xterm  (Abstr(var, Signature.bt_o,Appl(Symbol "~",var)))))] in
   let term1 = (xterm2term (substitute st.index term binding1)) and
       term2 = (xterm2term (substitute st.index term binding2)) and
       term3 = (xterm2term (substitute st.index term binding3)) and
       term4 = (xterm2term (substitute st.index term binding4)) in 
   if flag 
   then [(term2xterm term1); (term2xterm term2); (term2xterm term3); (term2xterm term4)]
   else [(term2xterm (sOr (sOr term1 term2) (sOr term3 term4)))]

let special_instantiation_o_o_o (nvar:role xterm) (term:role xterm) st flag = 
   let x = create_and_insert_new_free_var (Symbol "X") Signature.bt_o st in
   let y = create_and_insert_new_free_var (Symbol "X") Signature.bt_o st in
   let binding0 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(Symbol cfalse)))))))] and
       binding1 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sAnd (sNeg x) (sNeg y))))))))] and
       binding2 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sAnd (sNeg x) y)))))))] and
       binding3 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sNeg x)))))))] and
       binding4 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sAnd x (sNeg y))))))))] and
       binding5 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sNeg y)))))))] and
       binding6 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sOr (sAnd x (sNeg y)) (sAnd (sNeg x) y))))))))] and
       binding7 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sNeg (sAnd x y))))))))] and
       binding8 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sAnd x y)))))))] and
       binding9 =  [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sOr (sAnd x y) (sAnd (sNeg x) (sNeg y)))))))))] and
       binding10 = [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,x))))))] and
       binding11 = [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sNeg (sAnd x (sNeg y)))))))))] and
       binding12 = [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,y))))))] and
       binding13 = [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sNeg (sAnd (sNeg x) y))))))))] and
       binding14 = [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(sOr x y)))))))] and
       binding15 = [(nvar,(term2xterm  (Abstr(x,Signature.bt_o,(Abstr(y,Signature.bt_o,(Symbol ctrue)))))))] in
   let t0 = (xterm2term (substitute st.index term binding0)) and
       t1 = (xterm2term (substitute st.index term binding1)) and 
       t2 = (xterm2term (substitute st.index term binding2)) and
       t3 = (xterm2term (substitute st.index term binding3)) and 
       t4 = (xterm2term (substitute st.index term binding4)) and
       t5 = (xterm2term (substitute st.index term binding5)) and 
       t6 = (xterm2term (substitute st.index term binding6)) and
       t7 = (xterm2term (substitute st.index term binding7)) and 
       t8 = (xterm2term (substitute st.index term binding8)) and
       t9 = (xterm2term (substitute st.index term binding9)) and 
       t10 = (xterm2term (substitute st.index term binding10)) and
       t11 = (xterm2term (substitute st.index term binding11)) and 
       t12 = (xterm2term (substitute st.index term binding12)) and
       t13 = (xterm2term (substitute st.index term binding13)) and 
       t14 = (xterm2term (substitute st.index term binding14)) and
       t15 = (xterm2term (substitute st.index term binding15)) in
    if flag 
    then   
     [(term2xterm t0); (term2xterm t1); (term2xterm t2); (term2xterm t3);
      (term2xterm t4); (term2xterm t5); (term2xterm t6); (term2xterm t7);
      (term2xterm t8); (term2xterm t9); (term2xterm t10); (term2xterm t11);
      (term2xterm t12); (term2xterm t13); (term2xterm t14); (term2xterm t15)]
    else
     [(term2xterm 
        (sOr (sOr (sOr (sOr t0 t1) (sOr t2 t3))
     		  (sOr (sOr t4 t5) (sOr t6 t7)))
	     (sOr (sOr (sOr t8 t9) (sOr t10 t11))
		  (sOr (sOr t12 t13) (sOr t14 t15)))))]


let special_instantiation_oo_o (nvar:role xterm) (term:role xterm) st flag = 
   let ty_oo = (Funtype(Signature.bt_o,Signature.bt_o)) in
   let f = create_and_insert_new_free_var (Symbol "X") ty_oo st in
   let x = create_and_insert_new_free_var (Symbol "X") Signature.bt_o st in
   let f_oo_1 = (sAll x Signature.bt_o (Appl(f,x))) in
   let f_oo_2 = (sAll x Signature.bt_o (sNeg (Appl(f,x)))) in
   let f_oo_3 = (sAnd (Appl(f,(Symbol ctrue))) (sNeg (Appl(f,(Symbol cfalse))))) in
   let f_oo_4 = (sAnd (sNeg (Appl(f,(Symbol ctrue)))) (Appl(f,(Symbol cfalse)))) in
   let binding0  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(Symbol cfalse)))))] and
       binding1  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,f_oo_1))))] and
       binding2  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,f_oo_2))))] and
       binding3  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,f_oo_3))))] and
       binding4  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,f_oo_4))))] and
       binding5  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_1 f_oo_2)))))] and
       binding6  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_1 f_oo_3)))))] and
       binding7  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_1 f_oo_4)))))] and
       binding8  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_2 f_oo_3)))))] and
       binding9  =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_2 f_oo_4)))))] and
       binding10 =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_3 f_oo_4)))))] and
       binding11 =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_1 (sOr f_oo_2 f_oo_3))))))] and
       binding12 =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_1 (sOr f_oo_2 f_oo_4))))))] and
       binding13 =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(sOr f_oo_2 (sOr f_oo_3 f_oo_4))))))] and
       binding14 =  [(nvar,(term2xterm  (Abstr(f,ty_oo,(Symbol ctrue)))))] in 
   let t0 = (xterm2term (substitute st.index term binding0)) and
       t1 = (xterm2term (substitute st.index term binding1)) and 
       t2 = (xterm2term (substitute st.index term binding2)) and
       t3 = (xterm2term (substitute st.index term binding3)) and 
       t4 = (xterm2term (substitute st.index term binding4)) and
       t5 = (xterm2term (substitute st.index term binding5)) and 
       t6 = (xterm2term (substitute st.index term binding6)) and
       t7 = (xterm2term (substitute st.index term binding7)) and 
       t8 = (xterm2term (substitute st.index term binding8)) and
       t9 = (xterm2term (substitute st.index term binding9)) and 
       t10 = (xterm2term (substitute st.index term binding10)) and
       t11 = (xterm2term (substitute st.index term binding11)) and 
       t12 = (xterm2term (substitute st.index term binding12)) and
       t13 = (xterm2term (substitute st.index term binding13)) and 
       t14 = (xterm2term (substitute st.index term binding14)) in
    if flag 
    then   
     [(term2xterm t0); (term2xterm t1); (term2xterm t2); (term2xterm t3);
      (term2xterm t4); (term2xterm t5); (term2xterm t6); (term2xterm t7);
      (term2xterm t8); (term2xterm t9); (term2xterm t10); (term2xterm t11);
      (term2xterm t12); (term2xterm t13); (term2xterm t14)]
    else
     [(term2xterm 
        (sOr (sOr (sOr (sOr t0 t1) (sOr t2 t3))
     		  (sOr (sOr t4 t5) (sOr t6 t7)))
	     (sOr (sOr (sOr t8 t9) (sOr t10 t11))
		  (sOr (sOr t12 t13) t14))))]


let contains_choice_hd (xt:role xterm) st = false
(*
    Util.sysout 3 ( "\n\n HAS_CHOICE_HD: "^(to_string xt));
    let t = (xterm2term xt) in
    let result =
       match t with
         Appl(_,_) -> 
            let xhd = (get_head xt) in
            let hd = (xterm2term xhd) in
               (match type_of xhd with
                   Funtype(Funtype(alpha,Basetype("$o")),beta) ->
	             alpha = beta && (List.mem hd st.choice_functions || Term.is_variable hd)
	         | _ -> false)
        | _ -> false in
      Util.sysout 3 ( "\n HAS_CHOICE_HD Result: "^(string_of_bool result));
      result
*)

let normalize_lit (l:role lit_literal) (st:state)  (free_vars:term list) =
  Util.sysout 3 ("\n\n Normalizing lit: "^(lit_literal_to_string l)^"\n\n"); 
  if l.lit_polarity (* positive literal *) 
  then
    match (xterm2im l.lit_term 3) with
      Xappl(Xsymbol ("~",_),t1,_) ->
        ([lit_mk_neg_literal st.signature (im2xterm t1)],[],[],"extcnf_not_pos",[])
    | Xappl(Xappl(Xsymbol ("|",_),t1,_),t2,_) ->
        ([lit_mk_pos_literal st.signature (im2xterm t1);
          lit_mk_pos_literal st.signature (im2xterm t2)],[],[],"extcnf_or_pos",[])
    | Xappl(Xsymbol ("!",_),t1,_) -> 
	let (term,nvar) =  (free_var_term (im2term t1) st) in 
	let (xterm,xnvar) = ((term2xterm term),(term2xterm nvar)) in 
   let ty = type_of xnvar in
    if ty = Signature.bt_o  then
      ([], [], [], "extcnf_forall_special_pos",
       [lit_mk_pos_literal st.signature (term2xterm term)] ::
         (List.map (fun l -> [lit_mk_pos_literal st.signature l])
            (special_instantiation_o xnvar xterm st true)))
    else if ty = Funtype (Signature.bt_o, Signature.bt_o)   then
      ([], [], [], "extcnf_forall_special_pos",
       [lit_mk_pos_literal st.signature (term2xterm term)]
         ::(List.map (fun l -> [lit_mk_pos_literal st.signature l])
              (special_instantiation_o_o xnvar xterm st true)))
    else if ty = Funtype (Signature.bt_o, Funtype (Signature.bt_o, Signature.bt_o))  then
      ([], [], [], "extcnf_forall_special_pos",
        [lit_mk_pos_literal st.signature (term2xterm term)]
         ::(List.map (fun l -> [lit_mk_pos_literal st.signature l])
             (special_instantiation_o_o_o xnvar xterm st true)))
(*  this seems too exhaustive
    else if ty = Funtype (Funtype (Signature.bt_o, Signature.bt_o), Signature.bt_o)  then
      ([], [], [], "extcnf_forall_special_pos",
        [lit_mk_pos_literal (term2xterm term)]
         ::(List.map (fun l -> [lit_mk_pos_literal l])
             (special_instantiation_oo_o xnvar xterm st true)))
*)
    else ([lit_mk_pos_literal st.signature (term2xterm term)], [], [nvar],
          "extcnf_forall_pos", [])
    | Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	      ([lit_mk_pos_literal st.signature (ext_rewrite_equation l1 l2 st)],
         [lit_mk_eq_literal st.signature (im2xterm l1) (im2xterm l2) "cnf-touched"],
         [],"extcnf_equal_pos",[])
    | _ -> ([l],[],[],"extcnf_equal_pos",[])
  else (*negative literal*)
    match (xterm2im l.lit_term 3) with
        Xappl(Xsymbol ("~",_),t1,_) ->
          ([lit_mk_pos_literal st.signature (im2xterm t1)],[],[],"extcnf_not_neg",[])
      | Xappl(Xappl(Xsymbol ("|",_),t1,_),t2,_) ->
          ([lit_mk_neg_literal st.signature (im2xterm t1)],
           [lit_mk_neg_literal st.signature (im2xterm t2)],[],"extcnf_or_neg",[])
      | Xappl(Xsymbol ("!",_),t1,_) ->
(*
	let (term,nvar) =  (free_var_term (im2term t1) st) in 
	let (xterm,xnvar) = ((term2xterm term),(term2xterm nvar)) in 
   let ty = type_of xnvar in
    if ty = Signature.bt_o  then
      ([], [], [], "extcnf_forall_special_neg",
       [lit_mk_neg_literal (term2xterm (skolem_term (im2term t1) st free_vars))]
         ::[(List.map (fun l -> lit_mk_neg_literal l)
              (special_instantiation_o xnvar xterm st true))])
    else if ty = Funtype (Signature.bt_o, Signature.bt_o)   then
      ([], [], [], "extcnf_forall_special_neg",
       [lit_mk_neg_literal (term2xterm (skolem_term (im2term t1) st free_vars))]
         ::[(List.map (fun l -> lit_mk_neg_literal l)
              (special_instantiation_o_o xnvar xterm st true))])
    else if ty = Funtype (Signature.bt_o, Funtype (Signature.bt_o, Signature.bt_o))  then
      ([], [], [], "extcnf_forall_special_neg",
        [lit_mk_neg_literal (term2xterm (skolem_term (im2term t1) st free_vars))]
         ::[(List.map (fun l -> lit_mk_neg_literal l)
             (special_instantiation_o_o_o xnvar xterm st true))])
    else 
*)
          ([lit_mk_neg_literal st.signature (term2xterm (skolem_term (im2term t1) st free_vars))], [], [],
           "extcnf_forall_neg", [])
      | Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	        ([lit_mk_neg_literal st.signature (ext_rewrite_equation l1 l2 st)],
           [lit_mk_uni_literal st.signature (im2xterm l1) (im2xterm l2) "cnf-touched"],[],"extcnf_equal_neg",[])
      | _ -> ([l],[],[],"extcnf_equal_neg",[])


(*
let normalize_lit (l:role lit_literal) (st:state)  (free_vars:term list) =
  let atom = (xterm2term l.lit_term) in
  if l.lit_polarity (* positive literal *) 
  then 
    match atom with
      Appl(Symbol "~",t1) -> ([lit_mk_neg_literal (term2xterm t1)],[],[])
    | Appl(Appl(Symbol "|",t1),t2) -> ([lit_mk_pos_literal (term2xterm t1);lit_mk_pos_literal (term2xterm t2)],[],[])
    | Appl(Appl(Symbol "=",t1),t2) -> 
	([lit_mk_pos_literal (ext_rewrite_equation t1 t2 st)],[lit_mk_eq_literal (term2xterm t1) (term2xterm t2) "cnf-touched"],[])
    | Appl(Symbol "!",t1) -> 
	let (term,nvar) =  (free_var_term t1 st) in ([lit_mk_pos_literal (term2xterm term)],[],[nvar])
    | _ -> ([l],[],[])
  else (*negative literal*)
    match atom with
      Appl(Symbol "~",t1) -> ([lit_mk_pos_literal (term2xterm t1)],[],[])
    | Appl(Appl(Symbol "|",t1),t2) -> ([lit_mk_neg_literal (term2xterm t1)],[lit_mk_neg_literal (term2xterm t2)],[])
    | Appl(Appl(Symbol "=",t1),t2) -> 
	([lit_mk_neg_literal (ext_rewrite_equation t1 t2 st)],[lit_mk_uni_literal (term2xterm t1) (term2xterm t2) "cnf-touched"],[])
    | Appl(Symbol "!",Abstr(var,ty,Appl(Symbol "~",Appl(Symbol "~",t1)))) ->
	([lit_mk_neg_literal (term2xterm (Appl(Symbol "!",Abstr(var,ty,t1))))],[],[])
    | Appl(Symbol "!",Abstr(var,ty,Appl(Appl(Symbol "|",t1),t2))) ->
	(
	 let test1 = (occurs_in st.index (term2xterm t1) (term2xterm var)) 
	 and test2 = (occurs_in st.index (term2xterm t2) (term2xterm var)) in
	 match (test1,test2) with
	   (true,false) -> ([lit_mk_neg_literal (term2xterm  (Appl(Appl(Symbol "|",Appl(Symbol "!",Abstr(var,ty,t1))),t2)))],[],[])
	 | (false,true) -> ([lit_mk_neg_literal (index st.index (term2xterm  (Appl(Appl(Symbol "|",t1),Appl(Symbol "!",Abstr(var,ty,t2))))))],[],[])
	 | _ -> 
	     let free_vars =  List.map (fun v -> (Symbol v)) (Term.free_vars (Abstr(var,ty,Appl(Appl(Symbol "|",t1),t2)))) in
             ([lit_mk_neg_literal (term2xterm (skolem_term (Abstr(var,ty,Appl(Appl(Symbol "|",t1),t2))) st free_vars))],[],[])
	)
    | Appl(Symbol "!",Abstr(var,ty,Appl(Symbol "~",Appl(Appl(Symbol "|",t1),t2)))) ->
	(
	 let test1 = (occurs_in st.index (term2xterm t1) (term2xterm var)) 
	 and test2 = (occurs_in st.index (term2xterm t2) (term2xterm var)) in
	 match (test1,test2) with
	   (true,false) -> ([lit_mk_neg_literal (term2xterm (Appl(Symbol "~",Appl(Appl(Symbol "|",Appl(Symbol "~",Appl(Symbol "!",Abstr(var,ty,(Appl(Symbol "~",t1)))))),t2))))],[],[])
	 | (false,true) -> ([lit_mk_neg_literal (term2xterm (Appl(Symbol "~",Appl(Appl(Symbol "|",t1),Appl(Symbol "~",Appl(Symbol "!",Abstr(var,ty,(Appl(Symbol "~",t2)))))))))],[],[])
	 | _ -> 
	     let free_vars =  List.map (fun v -> (Symbol v)) (Term.free_vars (Abstr(var,ty,Appl(Symbol "~",Appl(Appl(Symbol "|",t1),t2))))) in
	     ([lit_mk_neg_literal (term2xterm (skolem_term (Abstr(var,ty,Appl(Symbol "~",Appl(Appl(Symbol "|",t1),t2)))) st free_vars))],[],[])
	)
    | Appl(Symbol "!",t1) -> ([lit_mk_neg_literal (term2xterm (skolem_term t1 st free_vars))],[],[])
    | _ -> ([l],[],[])
*)



(*
let normalize_lit (l:role lit_literal) (st:state)  (fv:term list) =
  if l.lit_polarity (* positive literal *) 
  then 
    match (xterm2im l.lit_term 7) with
      Xappl(Xsymbol ("~",_),t1,_) -> ([lit_mk_neg_literal (im2xterm t1)],[],[])
    | Xappl(Xappl(Xsymbol ("|",_),t1,_),t2,_) -> ([lit_mk_pos_literal (im2xterm t1);lit_mk_pos_literal (im2xterm t2)],[],[])
    | Xappl(Xappl(Xsymbol("=",_),t1,_),t2,_) -> 
	([lit_mk_pos_literal (ext_rewrite_equation (im2term t1) (im2term t2) st)],[lit_mk_eq_literal (im2xterm t1) (im2xterm t2) "cnf-touched"],[])
    | Xappl(Xsymbol ("!",_),t1,_) -> 
	let (term,nvar) =  (free_var_term (im2term t1) st) in ([lit_mk_pos_literal (term2xterm term)],[],[nvar])
    | _ -> ([l],[],[])
  else (*negative literal*)
    match (xterm2im l.lit_term 7) with
      Xappl(Xsymbol ("~",_),t1,_) -> ([lit_mk_pos_literal (im2xterm t1)],[],[]) 
    | Xappl(Xappl(Xsymbol ("|",_),t1,_),t2,_) -> ([lit_mk_neg_literal (im2xterm t1)],[lit_mk_neg_literal (im2xterm t2)],[]) 
    | Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	([lit_mk_neg_literal (ext_rewrite_equation (im2term l1) (im2term l2) st)],[lit_mk_uni_literal (im2xterm l1) (im2xterm l2) "cnf-touched"],[])
    | Xappl(Xsymbol ("!",_),Xabstr(var,_,Xappl(Xsymbol ("~",_),Xappl(Xsymbol ("~",_),t1,_),_),_),_) -> 
	let newterm = mk_appl (mk_const "!") (mk_abs (im2xterm var) (type_of (im2xterm var)) (im2xterm t1)) in 
	([lit_mk_neg_literal newterm],[],[])
    | Xappl(Xsymbol ("!",_),Xabstr(var,_,Xappl(Xappl(Xsymbol ("|",_),t1,_),t2,_),_),_) ->
	(
	 let test1 = (occurs_in st.index (im2xterm t1) (im2xterm var)) 
	 and test2 = (occurs_in st.index (im2xterm t2) (im2xterm var)) in
	 match (test1,test2) with
	   (true,false) -> 
	     let newterm = (mk_appl 
			      (mk_appl 
				 (mk_const "|") 
				 (mk_appl (mk_const "!") (mk_abs (im2xterm var) (type_of (im2xterm var)) (im2xterm t1))))
			      (im2xterm t2)) 
	     in ([lit_mk_neg_literal newterm],[],[])
	 | (false,true) -> 
	     let newterm = (mk_appl 
			      (mk_appl (mk_const "|") (im2xterm t1))
			      (mk_appl (mk_const "!") (mk_abs (im2xterm var) (type_of (im2xterm var)) (im2xterm t2)))) 
	     in ([lit_mk_neg_literal newterm],[],[])
	 | _ ->
	     (
	      match (xterm2im l.lit_term 3) with
		Xappl(Xsymbol ("!",_),t1,_) -> 
		  let freevars = free_vars l.lit_term in
		  ([lit_mk_neg_literal (term2xterm (skolem_term (im2term t1) st freevars))],[],[])
	      | _ -> raise (Failure "Bug in normalize_lit")
	     )
	)
    | Xappl(Xsymbol ("!",_),Xabstr(var,_,Xappl(Xsymbol ("~",_),Xappl(Xappl(Xsymbol ("|",_),t1,_),t2,_),_),_),_) ->
	(
	 let test1 = (occurs_in st.index (im2xterm t1) (im2xterm var)) 
	 and test2 = (occurs_in st.index (im2xterm t2) (im2xterm var)) in
	 match (test1,test2) with
	   (true,false) -> 
	     let newterm = (mk_appl
			      (mk_appl 
				 (mk_const "|") 
				 (mk_appl 
				    (mk_const "~")
				    (mk_appl 
				       (mk_const "!") 
				       (mk_abs 
					  (im2xterm var) (type_of (im2xterm var)) 
					  (mk_appl 
					     (mk_const "~") 
					     (im2xterm t1))))))
			      (im2xterm t2)) 
	     in ([lit_mk_neg_literal newterm],[],[])
	 | (false,true) -> 
	     let newterm = (mk_appl
			      (im2xterm t1)
			      (mk_appl 
				 (mk_const "|") 
				 (mk_appl 
				    (mk_const "~")
				    (mk_appl 
				       (mk_const "!") 
				       (mk_abs 
					  (im2xterm var) (type_of (im2xterm var)) 
					  (mk_appl 
					     (mk_const "~") 
					     (im2xterm t2)))))))			      
	     in ([lit_mk_neg_literal newterm],[],[])
	 | _ ->
	     (
	      match (xterm2im l.lit_term 3) with
		Xappl(Xsymbol ("!",_),t1,_) -> 
		  let freevars = free_vars l.lit_term in
		  ([lit_mk_neg_literal (term2xterm (skolem_term (im2term t1) st freevars))],[],[])
	      | _ -> raise (Failure "Bug in normalize_lit")
	     )
	)
    | Xappl(Xsymbol ("!",_),t1,_) -> 
	let freevars = free_vars l.lit_term in
	([lit_mk_neg_literal (term2xterm (skolem_term (im2term t1) st freevars))],[],[])
    | _ -> ([l],[],[])
*)





let lit_is_normalizable (l:role lit_literal) =
(*  Util.sysout 3 ("\n\n Testing "^(lit_literal_to_string l)); *)
  match (xterm2term l.lit_term) with   
    Appl(Symbol "~",_) -> true
  | Appl(Appl(Symbol "|",_),_) -> true
  | Appl(Symbol "!",_) -> true
  | Appl(Appl(Symbol "=",l1),_) -> 
      (
       if (l.lit_info = "cnf-touched") then false
       else
         let ty = type_of (term2xterm l1)
         in ty = Signature.bt_o || Hol_type.is_funtype ty
      )
  | _ -> false



let find_first_and_split (p:role lit_literal -> bool) (ll:role lit_literal list) (accu:role lit_literal list) =
  let rec internal (p:role lit_literal -> bool) (ll:role lit_literal list) (accu:role lit_literal list) =
    match ll with
      [] -> raise Literal_not_found
    | hd::tl -> if p hd then (hd,(accu@tl)) else (internal p tl (hd::accu))
  in
  internal p ll []

 
let normalize_first_lit (ll:role lit_literal list) (st:state) (fv:term list) =
  let (l,rl) = find_first_and_split lit_is_normalizable ll [] in
  let triple = normalize_lit l st fv in
  match triple with
    (l1,[],nfv,info,[]) -> ([(l1@rl)],nfv,info)
  | (l1,l2,nfv,info,[]) -> ([(l1@rl);(l2@rl)],nfv,info)
  | ([],[],nfv,info,l1)  -> ((List.map (fun lit -> (lit@rl)) l1),nfv,info)
  | _ -> raise (Calculus_failure "normalize_first_lit")

let litlist_free_vars (ll:'a lit_literal list) =
  let res = ref [] in
  let rec litlist_free_vars' (ll:'a lit_literal list) =
    match ll with
     [] -> ()
   | hd::tl -> 
       let freevars = Term.free_vars (xterm2term hd.lit_term) in
       List.iter 
	 (fun v -> 
	   if List.exists (fun x -> v = x) !res 
	   then () 
	   else res := v::(!res))
	 freevars;
       litlist_free_vars' tl
  in
  litlist_free_vars' ll;
  List.map (fun v -> (Symbol v)) !res



let cnf_normalize_step (c:cl_clause) (st:state) =
  Util.sysout 3 ("\n\  CNF-STEP: "^(cl_clause_to_protocol c)); 
 try 
   match normalize_first_lit (Array.to_list c.cl_litarray) st c.cl_free_vars with
      (list,nfv,info) -> (* recompute the information on free variables *)
       	let result = 
      	 (List.map 
          (fun ll -> 	      
            let nfv1 = litlist_free_vars ll in
	    (mk_clause ll (inc_clause_count st) nfv1 (info,[(c.cl_number,"")],"") c.cl_origin st))
           list) in
         Util.sysout 3 ("\n\  CNF-STEP: "^(cl_clause_to_protocol c)^"  CNF-STEP-RESULT: "^(cl_clauselist_to_protocol result)^"\n");
	 result	
 with
   Literal_not_found -> 
     let result = [c] in
     Util.sysout 3 ("  CNF-STEP-RESULT: "^(cl_clauselist_to_protocol result)^"\n");
     result

(*
let cnf_normalize_clauseset (cls:Set_of_clauses.t) (st:state) =
  let cll = Set_of_clauses.elements cls in
  List.concat (List.map (fun c -> cnf_normalize_step c st) cll)  
      
let cnf_exhaustively_normalize_clauselist (cll:cl_clause list) (st:state) =
  let rec cnf_exhaustively_normalize_clauselist_help (cll:cl_clause list) (st:state) (accu:cl_clause list) =
    match cll with
      [] -> accu
    | hd::tl -> 
	let count = st.clause_count in 
	let rl = cnf_normalize_step hd st inexhaustive (raise_to_list flex_rigid)
	if count >= st.clause_count (* termination *) 
	then cnf_exhaustively_normalize_clauselist_help tl st (rl@accu)
	else cnf_exhaustively_normalize_clauselist_help (rl@tl) st accu
  in
  cnf_exhaustively_normalize_clauselist_help cll st []

let cnf_exhaustively_normalize  (cl:cl_clause) (st:state) =
  cnf_exhaustively_normalize_clauselist [cl] st

let cnf_exhaustively_normalize_clauseset (cls:Set_of_clauses.t) (st:state) =
  cnf_exhaustively_normalize_clauselist (Set_of_clauses.elements cls) st
*)



(* Standard CNF: new June 2009 *)
      
let standard_extcnf_term term st =     (* see Nonnengart && Weidenbach 1999 *)

  let freevars t =  List.map (fun v -> (Symbol v)) (Term.free_vars t) in

  let rec simpl term st =   
    (
      match term with
	  Appl(Appl(Symbol "~|",t1),t2) -> simpl (Appl(Symbol "~",Appl(Appl(Symbol "|",t1),t2))) st
	| Appl(Appl(Symbol "~&",t1),t2) -> simpl (Appl(Symbol "~",Appl(Appl(Symbol "&",t1),t2))) st
	| Appl(Appl(Symbol "<~>",t1),t2) -> simpl (Appl(Symbol "~",Appl(Appl(Symbol "<=>",t1),t2))) st
	| Appl(Appl(Symbol "!=",t1),t2) -> simpl (Appl(Symbol "~",Appl(Appl(Symbol "=",t1),t2))) st
	| Appl(Appl(Symbol "<=",t1),t2) -> simpl (Appl(Appl(Symbol "=>",t2),t1)) st
	    
	|	Appl(Appl(Symbol "&",t),Symbol "$true") -> simpl t st
	| Appl(Appl(Symbol "&",Symbol "$true"),t) -> simpl t st
	    
	|	Appl(Appl(Symbol "&",t),Symbol "$false") -> Symbol "$false" 
	| Appl(Appl(Symbol "&",Symbol "$false"),t) -> Symbol "$false" 
	    
	|	Appl(Appl(Symbol "&",t1),Appl(Symbol "~",t2)) -> 
		  if t1 = t2 then Symbol "$false" else (Appl(Appl(Symbol "&",simpl t1 st),Appl(Symbol "~",simpl t2 st))) 
	| Appl(Appl(Symbol "&",Appl(Symbol "~",t1)),t2) -> 
	    if t1 = t2 then Symbol "$false" else (Appl(Appl(Symbol "&",Appl(Symbol "~",simpl t1 st)),simpl t2 st))
	      
	|	Appl(Appl(Symbol "&",t1),t2) -> 
		  if t1 = t2 then simpl t1 st else 
		    if smaller_head t1 t2 
		    then (Appl(Appl(Symbol "&",simpl t1 st),simpl t2 st))
		    else (Appl(Appl(Symbol "&",simpl t2 st),simpl t1 st))
		      
	|	Appl(Appl(Symbol "|",t),Symbol "$true") -> Symbol "$true"
	| Appl(Appl(Symbol "|",Symbol "$true"),t) -> Symbol "$true" 
	    
	|	Appl(Appl(Symbol "|",t),Symbol "$false") -> simpl t st
	| Appl(Appl(Symbol "|",Symbol "$false"),t) -> simpl t st
	    
	|	Appl(Appl(Symbol "|",t1),Appl(Symbol "~",t2)) ->  
		  if t1 = t2 then Symbol "$true" else (Appl(Appl(Symbol "|",simpl t1 st),Appl(Symbol "~",simpl t2 st)))
	| Appl(Appl(Symbol "|",Appl(Symbol "~",t1)),t2) ->  
	    if t1 = t2 then Symbol "$true" else (Appl(Appl(Symbol "|",Appl(Symbol "~",simpl t1 st)),simpl t2 st))
	      
	| Appl(Appl(Symbol "|",t1),t2) -> 
	    if t1 = t2 then simpl t1 st else 
	      if smaller_head t1 t2 
	      then (Appl(Appl(Symbol "|",simpl t1 st),simpl t2 st))
	      else (Appl(Appl(Symbol "|",simpl t2 st),simpl t1 st))
		
	| Appl(Symbol "~",Appl(Symbol "~",t)) -> simpl t st
	    
	| Appl(Appl(Symbol "~",t),Symbol "$true") -> Symbol "$false" 
	| Appl(Appl(Symbol "~",t),Symbol "$false") -> Symbol "$true" 
	    
	| Appl(Symbol "~",t) -> Appl(Symbol "~",simpl t st)
	    
	|	Appl(Appl(Symbol "=>",t),Symbol "$true") -> Symbol "$true"
	| Appl(Appl(Symbol "=>",Symbol "$true"),t) -> simpl t st
	    
	|	Appl(Appl(Symbol "=>",t),Symbol "$false") -> simpl (Appl(Symbol "~",t)) st
	| Appl(Appl(Symbol "=>",Symbol "$false"),t) -> Symbol "$true"
	    
	|	Appl(Appl(Symbol "=>",t1),t2) ->  
		  if t1 = t2 then Symbol "$true" else (Appl(Appl(Symbol "=>",simpl t1 st),simpl t2 st)) 
		    
	| Appl(Appl(Symbol "<=>",t),Symbol "$true") -> simpl t st
	| Appl(Appl(Symbol "<=>",Symbol "$true"),t) -> simpl t st
	    
	| Appl(Appl(Symbol "<=>",t),Symbol "$false") -> simpl (Appl(Symbol "~",t)) st
	| Appl(Appl(Symbol "<=>",Symbol "$false"),t) -> simpl (Appl(Symbol "~",t)) st
	    
	| Appl(Appl(Symbol "<=>",t1),t2) ->  
	    if t1 = t2 then Symbol "$true" else 
	      if smaller_head t1 t2 
	      then (Appl(Appl(Symbol "<=>",simpl t1 st),simpl t2 st))
	      else (Appl(Appl(Symbol "<=>",simpl t2 st),simpl t1 st))
		
	| Appl(Appl(Symbol "=",t1),t2) ->  
	    if t1 = t2 then Symbol "$true" else (Appl(Appl(Symbol "=",simpl t1 st),simpl t2 st))
	      (*
		(
		match Term.type_of (type_of_symbol st.signature) t1 with
		Funtype(ty1,ty2) ->
		let newvar = create_and_insert_new_free_var (Symbol "E") ty1 st in
		simpl (Appl(Symbol "!",(Abstr(newvar,ty1,Appl(Appl(Symbol "=",Appl(t1,newvar)),Appl(t2,newvar)))))) st
	      (* (Appl(Appl(Symbol "=",(Appl(t1,newvar)))),(Appl(t2,newvar))))))) st *)
   		| Basetype("$o") -> simpl (Appl(Appl(Symbol "<=>",t1),t2)) st
		| Basetype(_)-> 
		if smaller_head t1 t2 
		then (Appl(Appl(Symbol "=",simpl t1 st),simpl t2 st))
		else (Appl(Appl(Symbol "=",simpl t2 st),simpl t1 st))
		)
	      *)
	      
	| Appl(Symbol "!",Abstr(var,ty,t)) -> 
	  (* if st.flags.replace_leibniz then 
	    (* detect Leibniz-Equality and replace *)
	      (match t with
		  Appl(Appl(Symbol "=>",Appl(var1,t1)),Appl(var2,t2))
		| Appl(Appl(Symbol "<=",Appl(var1,t1)),Appl(var2,t2))
		| Appl(Appl(Symbol "<=>",Appl(var1,t1)),Appl(var2,t2))
		| Appl(Appl(Symbol "|",Appl(Symbol "~",Appl(var1,t1))),Appl(var2,t2))
		| Appl(Appl(Symbol "|",Appl(var1,t1)),Appl(Symbol "~",Appl(var2,t2))) ->
		    (
		      if (var = var1) && (var = var2) then
			(Appl(Appl(Symbol "=",simpl t1 st),simpl t2 st))
		      else if List.mem var (freevars t) then (Appl(Symbol "!",Abstr(var,ty,simpl t st))) else simpl t st )
		| _ -> if List.mem var (freevars t) then (Appl(Symbol "!",Abstr(var,ty,simpl t st))) else simpl t st )
	    else *)
	      if List.mem var (freevars t) then (Appl(Symbol "!",Abstr(var,ty,simpl t st))) else simpl t st 
      
        | Appl(Symbol "?",Abstr(var,ty,t)) ->  
	    if List.mem var (freevars t) then (Appl(Symbol "?",Abstr(var,ty,simpl t st))) else simpl t st 
	      
	| Abstr(var,ty,t) -> Abstr(var,ty,simpl t st)
	| Symbol t -> Symbol t
	| t -> t
    ) in

  let rec nnf t =
    (
      let rec nf term =
	Util.sysout 3 ("\n nf term : "^(Term.to_hotptp term));
	match term with
	  | Appl(Symbol "~",Appl(Appl(Symbol "<=>",t1),t2)) -> 
	      nf (Appl(Symbol "~",(Appl(Appl(Symbol "|",(Appl(Appl(Symbol "&",t1),t2))),(Appl(Appl(Symbol "&",Appl(Symbol "~",t1)),Appl(Symbol "~",t2)))))))
		
	  | Appl(Appl(Symbol "<=>",t1),t2) -> 
	      nf (Appl(Appl(Symbol "&",(Appl(Appl(Symbol "=>",t1),t2))),(Appl(Appl(Symbol "=>",t2),t1))))
		
	  | Appl(Symbol "~",Appl(Appl(Symbol "&",t1),t2)) ->     
	      nf (Appl(Appl(Symbol "|",(Appl(Symbol "~",t1))),(Appl(Symbol "~",t2))))
		
	  | Appl(Symbol "~",Appl(Appl(Symbol "|",t1),t2)) ->     
	      nf (Appl(Appl(Symbol "&",(Appl(Symbol "~",t1))),(Appl(Symbol "~",t2))))
		
	  | Appl(Symbol "~",Appl(Symbol "!",Abstr(var,ty,t))) -> 
	      nf (Appl(Symbol "?",Abstr(var,ty,(Appl(Symbol "~",t)))))
		
	  | Appl(Symbol "~",Appl(Symbol "?",Abstr(var,ty,t))) -> 
	      nf (Appl(Symbol "!",Abstr(var,ty,(Appl(Symbol "~",t)))))
		
	  | Appl(Symbol "~",Appl(Appl(Symbol "=>",t1),t2)) ->     
	      nf (Appl(Appl(Symbol "&",t1),(Appl(Symbol "~",t2))))
		
	  | Appl(Appl(Symbol "=>",t1),t2) ->  
	      nf (Appl(Appl(Symbol "|",(Appl(Symbol "~",t1))),t2))
		
	  | Appl(Symbol "~",Appl(Symbol "~",t)) -> nf t
	      
	  | Appl(Appl(Symbol "|",Appl(Appl(Symbol "&",t1),t2)),t3) ->  
	      nf (Appl(Appl(Symbol "&",(Appl(Appl(Symbol "|",t1),t3))),(Appl(Appl(Symbol "|",t2),t3))))
		
	  | Appl(Appl(Symbol "|",t1),Appl(Appl(Symbol "&",t2),t3)) ->  
	      nf (Appl(Appl(Symbol "&",(Appl(Appl(Symbol "|",t1),t2))),(Appl(Appl(Symbol "|",t1),t3))))
		
	  | Appl(Appl(Symbol "|",t1),t2) ->  
	      (Appl(Appl(Symbol "|",nf t1),nf t2))
		
	  | Appl(Appl(Symbol "&",t1),t2) ->  
	      (Appl(Appl(Symbol "&",nf t1),nf t2))
		
	  | Appl(Symbol "!",Abstr(var,ty,t)) -> 
	      (Appl(Symbol "!",Abstr(var,ty,nf t)))
		
	  | Appl(Symbol "?",Abstr(var,ty,t)) -> 
	      (Appl(Symbol "?",Abstr(var,ty,nf t)))
		
		
	  (*	| Appl(t1,t2) -> Appl(nf t1,nf t2)
		
		| Abstr(var,ty,t) -> Abstr(var,ty,nf t)  *)
		
	  | t -> t
      in 
	Util.sysout 3 ("\n Enter nf term : "^(Term.to_hotptp term));
	let new_t = (nf t) in 
	  Util.sysout 3 ("\n Return nf term : "^(Term.to_hotptp new_t));
	  if new_t = t then new_t else nnf new_t 
    ) in

  let miniscope st term =
    (
      let rec ms st term = 
	Util.sysout 3 ("\n ms term : "^(Term.to_hotptp term));
	match term with
	    Appl(Symbol "!",Abstr(var,ty,Appl(Appl(Symbol "&",t1),t2))) ->  
	      (
		match ((List.mem var (freevars t1)),(List.mem var (freevars t2))) with
		    (false,false) ->   (Appl(Appl(Symbol "&",t1),t2))
		  | (true,false) ->  (Appl(Appl(Symbol "&",ms st (Appl(Symbol "!",Abstr(var,ty,t1)))),ms st t2))
		  | (false,true) ->  (Appl(Appl(Symbol "&",ms st t1),ms st (Appl(Symbol "!",Abstr(var,ty,t2)))))
		  | (true,true) -> (Appl(Appl(Symbol "&",ms st (Appl(Symbol "!",Abstr(var,ty,t1)))),ms st (Appl(Symbol "!",Abstr(var,ty,t2)))))
		      (* renaming deactivated
			 let newvar = create_and_insert_new_free_var_with_simple_name (Term.type_of (type_of_symbol st.signature) var) st in
			 let newt2  = xterm2term (substitute st.index (term2xterm t2) [((term2xterm var),(term2xterm newvar))]) in
			 (Appl(Appl(Symbol "&",ms st (Appl(Symbol "!",Abstr(var,ty,t1)))),ms st (Appl(Symbol "!",Abstr(newvar,ty,newt2)))))
		      *)
	      )
	  | Appl(Symbol "!",Abstr(var,ty,Appl(Appl(Symbol "|",t1),t2))) ->  
	      (
		match ((List.mem var (freevars t1)),(List.mem var (freevars t2))) with
		    (false,false) ->   (Appl(Appl(Symbol "|",t1),t2))
		  | (true,false) ->  (Appl(Appl(Symbol "|",ms st (Appl(Symbol "!",Abstr(var,ty,t1)))),ms st t2))
		  | (false,true) ->  (Appl(Appl(Symbol "|",ms st t1),ms st (Appl(Symbol "!",Abstr(var,ty,t2)))))
		  | (true,true) -> (Appl(Symbol "!",Abstr(var,ty,Appl(Appl(Symbol "|",ms st t1),ms st t2))))
	      )
	  | Appl(Symbol "?",Abstr(var,ty,Appl(Appl(Symbol "&",t1),t2))) ->  
	      (
		match ((List.mem var (freevars t1)),(List.mem var (freevars t2))) with
		    (false,false) ->   (Appl(Appl(Symbol "&",t1),t2))
		  | (true,false) ->  (Appl(Appl(Symbol "&",ms st (Appl(Symbol "?",Abstr(var,ty,t1)))),ms st t2))
		  | (false,true) ->  (Appl(Appl(Symbol "&",ms st t1),ms st (Appl(Symbol "?",Abstr(var,ty,t2)))))
		  | (true,true) -> (Appl(Symbol "?",Abstr(var,ty,Appl(Appl(Symbol "&",ms st t1),ms st t2))))
	      )
	  | Appl(Symbol "?",Abstr(var,ty,Appl(Appl(Symbol "|",t1),t2))) ->  
	      (
		match ((List.mem var (freevars t1)),(List.mem var (freevars t2))) with
		    (false,false) ->   (Appl(Appl(Symbol "|",t1),t2))
		  | (true,false) ->  (Appl(Appl(Symbol "|",ms st (Appl(Symbol "?",Abstr(var,ty,t1)))),ms st t2))
		  | (false,true) ->  (Appl(Appl(Symbol "|",ms st t1),ms st (Appl(Symbol "?",Abstr(var,ty,t2)))))
		  | (true,true) -> (Appl(Appl(Symbol "|",ms st (Appl(Symbol "?",Abstr(var,ty,t1)))),ms st (Appl(Symbol "?",Abstr(var,ty,t2)))))
		      (* renaming deactivated
			 let newvar = create_and_insert_new_free_var_with_simple_name (Term.type_of (type_of_symbol st.signature) var) st in
			 let newt2  = xterm2term (substitute st.index (term2xterm t2) [((term2xterm var),(term2xterm newvar))]) in
			 (Appl(Appl(Symbol "|",ms st (Appl(Symbol "?",Abstr(var,ty,t1)))),ms st (Appl(Symbol "?",Abstr(newvar,ty,newt2)))))
		      *)
	      )
	  | Appl(t1,t2) -> Appl(ms st t1,ms st t2)
	  | Abstr(var,ty,t) -> Abstr(var,ty,ms st t)  
	  | t -> t
      in
	Util.sysout 3 ("\n Enter ms term : "^(Term.to_hotptp term));
	let new_term = (ms st term) in 
	  if new_term = term 
	  then (Util.sysout 3 ("\n Return ms term : "^(Term.to_hotptp new_term)); new_term) 
	  else ms st new_term 
    ) in

  let standard_skolemize st term =
    (
      let rec sko st term freevars freevars_types = 
	Util.sysout 3 ("\n sko term : "^(Term.to_hotptp term));
	match term with
	    Appl(Symbol "!",Abstr(var,ty,t)) -> (Appl(Symbol "!",Abstr(var,ty,sko st t (var::freevars) (ty::freevars_types))))
	  | Appl(Symbol "?",Abstr(var,ty,t)) -> 
	      let sk_const_ty = List.fold_right (fun t1 t2 -> abstr_type t1 t2) freevars_types ty in
	      let skoconst = create_and_insert_skolem_const var sk_const_ty st in
	      let skoterm =  List.fold_left (fun t1 t2 -> Appl(t1,t2)) skoconst freevars in
		sko st (beta_normalize (Appl(Abstr(var,ty,t),skoterm))) freevars freevars_types
	  | Appl(Appl(Symbol "|",t1),t2)     -> Appl(Appl(Symbol "|",sko st t1 freevars freevars_types),sko st t2 freevars freevars_types)
	  | Appl(Appl(Symbol "&",t1),t2)     -> Appl(Appl(Symbol "&",sko st t1 freevars freevars_types),sko st t2 freevars freevars_types)
	  | t -> t
      in
	Util.sysout 3 ("\n Enter sko term : "^(Term.to_hotptp term));
	let new_term = (sko st term [] []) in 
	  Util.sysout 3 ("\n Return sko term : "^(Term.to_hotptp new_term));
	  new_term
    ) in
      
  let rename st term = 
(* 10/2009 dump copy and paste error fixed in the first actual renaming case below *)
    (
      let rec ren st term = 
	Util.sysout 3 ("\n ren term : "^(Term.to_hotptp term));
	match term with
	    Appl(Appl(Symbol "&",t1),t2)     -> (Appl(Appl(Symbol "&",ren st t1),ren st t2))
	  | Appl(Appl(Symbol "|",Appl(Appl(Symbol "&",t1),t2)),t3) -> 
	      let newprop = create_and_insert_skolem_const (Symbol "REN") bt_o st in
		(Appl(Appl(Symbol "&",Appl(Appl(Symbol "|",newprop),t3)),Appl(Appl(Symbol "=>",newprop),Appl(Appl(Symbol "&",t1),t2))))
	  | Appl(Appl(Symbol "|",t1),Appl(Appl(Symbol "&",t2),t3)) -> 
	      let newprop = create_and_insert_skolem_const (Symbol "REN") bt_o st in
		(Appl(Appl(Symbol "&",Appl(Appl(Symbol "|",t1),newprop)),Appl(Appl(Symbol "=>",newprop),Appl(Appl(Symbol "&",t2),t3))))
	  | t -> t
      in
	Util.sysout 3 ("\n Enter ren term : "^(Term.to_hotptp term));
	let new_term = (ren st term) in 
	  Util.sysout 3 ("\n Return ren term : "^(Term.to_hotptp new_term));
	  new_term
    ) in
    
    
    Util.sysout 3 ("\n *** term : "^(Term.to_hotptp term));
    let res_simpl = simpl term st in
    Util.sysout 3 ("\n *** res_simpl              : "^(Term.to_hotptp res_simpl));
    let res_nnf = nnf res_simpl in
    Util.sysout 3 ("\n *** res_nnf                : "^(Term.to_hotptp res_nnf));
    let res_miniscope = miniscope st res_nnf in
    Util.sysout 3 ("\n *** res_miniscope          : "^(Term.to_hotptp res_miniscope));
    let res_skolemize = standard_skolemize st res_miniscope in
    Util.sysout 3 ("\n *** res_skolemize          : "^(Term.to_hotptp res_skolemize));
    let res_rename = rename st res_skolemize in
    Util.sysout 3 ("\n *** res_rename             : "^(Term.to_hotptp res_rename));
      res_rename
		

let standard_extcnf (c:cl_clause) (st:state) =
  match (Array.to_list c.cl_litarray) with
      [l] ->
	if l.lit_polarity
	then 
	  let term = xterm2term l.lit_term in
	  let new_term = term2xterm (standard_extcnf_term term st) in 
	    if new_term = l.lit_term then [c] else 
	      let new_lit = lit_mk_pos_literal st.signature new_term
	      in 
		[mk_clause [new_lit] (inc_clause_count st) 
		   (c.cl_free_vars) ("extcnf_combined",[(c.cl_number,"")],"") c.cl_origin st]
	else raise (Failure "standard_extcnf")
    | _ -> raise (Failure "standard_extcnf")
	

(* The Skolemization Rule *)
(*
let standard_skolemize st term =
  let rec sko st term freevars freevars_types = 
    Util.sysout 3 ("\n sko term : "^(Term.to_hotptp term));
    match term with
	Appl(Symbol "!",Abstr(var,ty,t)) -> (Appl(Symbol "!",Abstr(var,ty,sko st t (var::freevars) (ty::freevars_types))))
      | Appl(Symbol "?",Abstr(var,ty,t)) -> 
	  let sk_const_ty = List.fold_right (fun t1 t2 -> abstr_type t1 t2) freevars_types ty in
	  let skoconst = create_and_insert_skolem_const var sk_const_ty st in
	  let skoterm =  List.fold_left (fun t1 t2 -> Appl(t1,t2)) skoconst freevars in
	    sko st (beta_normalize (Appl(Abstr(var,ty,t),skoterm))) freevars freevars_types
      | Appl(Appl(Symbol "|",t1),t2)     -> Appl(Appl(Symbol "|",sko st t1 freevars freevars_types),sko st t2 freevars freevars_types)
      | Appl(Appl(Symbol "&",t1),t2)     -> Appl(Appl(Symbol "&",sko st t1 freevars freevars_types),sko st t2 freevars freevars_types)
      | t -> t
  in
    Util.sysout 3 ("\n Enter sko term : "^(Term.to_hotptp term));
    let new_term = (sko st term [] []) in 
      Util.sysout 3 ("\n Return sko term : "^(Term.to_hotptp new_term));
      new_term
		
let rename (c:cl_clause) (st:state) =
*)

(* The Renaming Rule *)


let rename_pos st term =
  let rec ren st term = 
    Util.sysout 3 ("\n ren term : "^(Term.to_hotptp term));
    match term with
	Appl(Appl(Symbol "&",t1),t2)     -> (Appl(Appl(Symbol "&",ren st t1),ren st t2))
      | Appl(Appl(Symbol "|",Appl(Appl(Symbol "&",t1),t2)),t3) -> 
	  let newprop = create_and_insert_skolem_const (Symbol "REN") bt_o st in
	    (Appl(Appl(Symbol "&",Appl(Appl(Symbol "|",newprop),t3)),Appl(Appl(Symbol "=>",newprop),Appl(Appl(Symbol "&",t2),t3))))
      | Appl(Appl(Symbol "|",t1),Appl(Appl(Symbol "&",t2),t3)) -> 
	  let newprop = create_and_insert_skolem_const (Symbol "REN") bt_o st in
	    (Appl(Appl(Symbol "&",Appl(Appl(Symbol "|",t1),newprop)),Appl(Appl(Symbol "=>",newprop),Appl(Appl(Symbol "&",t2),t3))))
      | t -> t
  in
    Util.sysout 3 ("\n Enter ren term : "^(Term.to_hotptp term));
    let new_term = (ren st term) in 
      Util.sysout 3 ("\n Return ren term : "^(Term.to_hotptp new_term));
      new_term



let rename (c:cl_clause) (st:state) =
  match (Array.to_list c.cl_litarray) with
      [l] -> 
	if l.lit_polarity 
	then 
	  let term = xterm2term l.lit_term in
	  let new_term = term2xterm (rename_pos st term) in 
	  let new_lit = lit_mk_pos_literal st.signature new_term
	  in [mk_clause [new_lit] (inc_clause_count st) 
		(c.cl_free_vars) ("rename",[(c.cl_number,"")],"") c.cl_origin st]
	else [c]
    | _ -> raise (Failure "rename")



(** The Decomposition Rule *)

let rec dec_terms (l1:role xterm) (l2:role xterm) (accu:(role xintermediate * role xintermediate) list) =
  match ((xterm2im l1 3),(xterm2im l2 3)) with
      (* the first case here is new: June 16, 2010 *)
      (Xappl(Xappl(Xsymbol("=",_),s1,_),t1,_),Xappl(Xappl(Xsymbol("=",_),s2,_),t2,_)) -> 
	if (type_of (im2xterm s1)) = (type_of (im2xterm s2))  then
	  ((s1,s2)::((t1,t2)::accu))
	else []
    |  (Xappl(Xsymbol (s1,_),t1,_),Xappl(Xsymbol (s2,_),t2,_)) -> 
	 if  s1 = s2 && (type_of (im2xterm t1)) = (type_of (im2xterm t2)) && (not (s1 = disjunction))
	 then ((t1,t2)::accu) else []
    | (Xappl(h1,t1,_),Xappl(h2,t2,_)) -> 
	dec_terms (im2xterm h1) (im2xterm h2) ((t1,t2)::accu)
    | _ -> []
    
let dec_lit (l:role lit_literal) (st:state)=
  if l.lit_polarity then (false,[l]) else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
      if (is_basetype (type_of (im2xterm l1))) (* && (is_basetype (type_of (im2xterm l2))) *) 
      then
	let res =  (dec_terms (im2xterm l1) (im2xterm l2) []) in
	match res with
	  [] -> (false,[l])
	| _ -> 
	    (true,List.map 
	       (fun (t1,t2) -> 
		        lit_mk_uni_literal st.signature (im2xterm t1) (im2xterm t2) "dec")
	       res)
      else (false,[l])
  | _ -> (false,[l])

let decompose (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  DECOMPOSE: "^(cl_clause_to_protocol cl))); 
  let (flag,newlits) = 
    List.fold_right 
      (fun l (b,ll) -> let (nb,nll) = dec_lit l st in (b || nb,ll@nll))
      (Array.to_list cl.cl_litarray)
      (false,[])
  in 
  let result =
    if flag then 
      [mk_clause newlits (inc_clause_count st) 
	 (cl.cl_free_vars) ("dec",[(cl.cl_number,"")],"") cl.cl_origin st]
    else [] in
  output st (fun () -> ("  DECOMPOSE-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); 
  result

	
(*
let decompose_exhaustively (cl:cl_clause) (st:state) =
  let rec decompose_exhaustively_help (cll:cl_clause list) (st:state) (accu:cl_clause list) =
    match cll with
      [] -> accu
    | hd::tl -> 
	let count = st.clause_count in 
	let rl = decompose hd st in
	if count >= st.clause_count (* termination *) 
	then decompose_exhaustively_help tl st (rl@accu)
	else decompose_exhaustively_help (rl@tl) st accu
  in
  decompose_exhaustively_help [cl] st []
*)

(** The Substitute-or-Clash Unification Rule *)

(*
let lit_clash (l:role lit_literal) (st:state) =
  if l.lit_polarity then false else
  match (xterm2im l.lit_term 3) with
     Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
       (
	let t1 = (im2xterm l1) and t2 = (im2xterm l2) in
	if (is_variable t1) || (is_variable t2) 
	then (occurs_in st.index t1 t2) || (occurs_in st.index t2 t1)
	else true
       )
   | _ -> false

let clash_clause (cl:cl_clause) (st:state) =
  let flag = 
    List.fold_right 
      (fun l b -> (lit_clash l st) || b)
      (Array.to_list cl.cl_litarray)
      false
  in flag
*)

let clash_clause (cl:cl_clause) (st:state) = false

let rec subst_litlist (ll:(role lit_literal) list) (st:state) (flag,litlist,substpairlist) =
  match ll with
    [] -> (flag,litlist,substpairlist) 
   | l::rl  -> 
       if l.lit_polarity || flag then subst_litlist rl st (flag,l::litlist,substpairlist) else
       match (xterm2im l.lit_term 3) with
	  Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	    (
	     let t1 = (im2xterm l1) and t2 = (im2xterm l2) in
	     if is_variable t1 then subst_litlist rl st (true,litlist,(t1,t2)::substpairlist) else
	     if is_variable t2 then subst_litlist rl st (true,litlist,(t2,t1)::substpairlist) else
	     subst_litlist rl st (flag,l::litlist,substpairlist) 
	    )
	| _ -> subst_litlist rl st (flag,l::litlist,substpairlist)


let substitute_lit ?(info:string = "") (lit:role lit_literal) (st:state) substpairlist =
  if lit.lit_polarity then
    lit_mk_literal st.signature (substitute st.index lit.lit_term substpairlist) true info
  else
    lit_mk_literal st.signature (substitute st.index lit.lit_term substpairlist) false info

let subst_or_clash (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  SUBST-OR-CLASH: "^(cl_clause_to_protocol cl))); 
  let result =
    if clash_clause cl st then []
    else
      match subst_litlist (Array.to_list cl.cl_litarray) st (false,[],[]) with
	 (false,_,_) -> [cl] 
       | (true,ll,[(l1,l2)]) ->	
	   let newlits = List.map (fun l -> substitute_lit l st  [(l1,l2)]) ll
	   in
	   [mk_clause newlits (inc_clause_count st) 
	      (litlist_free_vars newlits) ("subst_or_clash",[(cl.cl_number,"")],"") cl.cl_origin st]
       | (_,_,_) -> raise (Failure "substitute_or_clash_clause") in
  output st (fun () -> ("  SUBST-OR-CLASH-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); 
  result


let instantiate substpairlist (cl:cl_clause) (st:state) =
  let newlits = List.map (fun l -> substitute_lit l st substpairlist) (Array.to_list cl.cl_litarray) in
  let subst_string_list = List.map (fun (v,t) -> ("bind("^(to_hotptp v)^",$thf("^(to_hotptp t)^"))")) substpairlist in
  let subst_string = 
   match subst_string_list with
      [] -> ""
    | hd::tl -> "["^(List.fold_left (fun s sub -> s^","^sub) hd tl)^"]" 
  in  
    mk_clause newlits (inc_clause_count st) (litlist_free_vars newlits)
     ("instantiate",[(cl.cl_number,subst_string)],"") cl.cl_origin st    



(*
let rec substitute_or_clash_clause_exhaustive (cl:cl_clause) (st:state) =
  try 
  match substitute_or_clash_clause cl st with 
    [] -> []
  | [newcl] -> 
      if newcl.cl_number = cl.cl_number then [newcl]
      else substitute_or_clash_clause_exhaustive newcl st
  | _ -> []
  with 
    Failure "Proof found" -> raise (Failure "Proof found")
  | Failure "Max clauses" -> raise (Failure "Max clauses")
  | Failure "Max loops" -> raise (Failure "Max loops")
  | Failure "Active empty" -> raise (Failure "Active empty")
  |  _ ->
      Util.sysout 3 ("error in substitute_or_clash_clause: "^(cl_clause_to_string (cl:cl_clause)));
      raise (Failure "substitute_or_clash_clause")
*)
(** Clause Factorzation *)

let clause_factorization st =
  let idx = st.index in
  let factorize = Hashtbl.create 10 in
  (* let rewrite = Hashtbl.create 10 in *)
  
  Hashtbl.iter
    (fun _ idset ->
     IdSet.iter
       (fun id ->
        let subsumed = lit_subsumes st id in
        if not (IdSet.is_empty subsumed) then 
         (let clns = List.map (fun (cln,_,_,_) -> cln) (Hashtbl.find_all st.index.role id) in
          (* Util.sysout 3 ("Term "^(string_of_int id)^":"^(term_to_hotptp st.index.termbase id)^"("^
            (List.fold_left (fun a b -> a^" "^(classify_role st b)) "" (Hashtbl.find_all st.index.role id))
             ^") subsumes:\n"); *)
          IdSet.iter (fun id2 -> let same = ref false in
                                let other = ref false in
                                List.iter
                                  (fun (cln,_,_,_) -> if List.mem cln clns
                                                      then (Hashtbl.add factorize cln (id,id2);
                                                            same := true)
                                                      else (Hashtbl.add factorize cln (id,id2);other := true))
                                  (Hashtbl.find_all st.index.role id2) (*;
                               
                                  let clpos =   (if (!same) then "same" else "")^
                                              (if (!same) && (!other) then "/" else "")^
                                              (if (!other) then "other" else "") in
                                  Util.sysout 3 ("  term "^(string_of_int id2)^":"^(term_to_hotptp st.index.termbase id2)^" ("^clpos^" clause)\n")*)
                                  ) 
                                  subsumed                               
       ))
       idset)    
    (Hashtbl.find idx.term_at_pos_role []);
    let clause_mods = Hashtbl.create (Hashtbl.length factorize) in
    Hashtbl.iter
      (fun cl (id1,id2) ->
         if Hashtbl.mem clause_mods cl
         then
           (let subsumes = Hashtbl.find clause_mods cl in
            if Hashtbl.mem subsumes id1 then
              (let lits = if Hashtbl.mem subsumes id2
                          then IdSet.add id2 (let l=Hashtbl.find subsumes id2 in
                                              Hashtbl.remove subsumes id2;
                                              l)
                          else IdSet.singleton id2 in
               Hashtbl.replace subsumes id1 (IdSet.union (Hashtbl.find subsumes id1) lits))
            else
            if Hashtbl.mem subsumes id2
            then
              (let lits = Hashtbl.find subsumes id2 in
               Hashtbl.remove subsumes id2;
               Hashtbl.add subsumes id1 (IdSet.add id2 lits))
            else Hashtbl.add subsumes id1 (IdSet.singleton id2))
         else
           (let subsumes = Hashtbl.create 1 in
            Hashtbl.add subsumes id1 (IdSet.singleton id2);
            Hashtbl.add clause_mods cl subsumes)  (*; 
         Util.sysout 3 ("In clause "^(string_of_int cl)^":\n");
         Util.sysout 3 ("  term "^(string_of_int id1)^":"^(term_to_hotptp st.index.termbase id1)^" subsumes \n");
         Util.sysout 3 ("  term "^(string_of_int id2)^":"^(term_to_hotptp st.index.termbase id2)^".\n")*)
      )
    factorize;
    Hashtbl.iter
      (fun cl subsumes ->
         Util.sysout 3 ("In clause "^(string_of_int cl)^":\n");
         (* remove self subsumption *)
         Hashtbl.iter
           (fun id1 lits -> if IdSet.mem id1 lits then Hashtbl.replace subsumes id1 (IdSet.remove id1 lits))
           subsumes;
         (* make substitutions *)
           let substs = Hashtbl.create 10 in
           Hashtbl.iter
             (fun id1 lits ->
               let lits = IdSet.remove id1 lits in
               let id1vars = varpoints st id1 [] in
               let subst_id1 = Hashtbl.create 1 in
               IdSet.iter
                 (fun id2 ->
                   let uni_clash = ref false in
                   let subst = Hashtbl.create (Hashtbl.length id1vars) in
                   Hashtbl.iter
                     (fun id poslist ->
                       List.iter 
                         (fun pos ->
                            let id_sub = occurs_at pos id2 st.index in
                            uni_clash := if id = id_sub then (!uni_clash) else
                                         if (Hashtbl.mem idx.occurrences id_sub) then
                                           (let oc=Hashtbl.find idx.occurrences id_sub in
                                            Hashtbl.mem oc id)
                                         else (!uni_clash);
                            if (not (id = id_sub)) then
                            let sub_final = ref id_sub in
                            Hashtbl.iter
                              (fun v rplc ->
                                sub_final := Substitution.apply_subst st.index  [(v,rplc)] (!sub_final)
                              )
                              subst;
                            (if Hashtbl.mem subst id && (not ((Hashtbl.find subst id) = id_sub)) then uni_clash := true;
                            if (not (!uni_clash)) && (not (Hashtbl.mem subst id)) then (
                            Hashtbl.iter
                              (fun v rplc -> Hashtbl.replace subst v (Substitution.apply_subst st.index  [(id,!sub_final)] rplc)
                              )
                              subst;         
                            Hashtbl.add subst id (!sub_final);
                            ))
                         )
                       poslist
                     )
                   id1vars;
                   if (not (!uni_clash)) then (
                     Hashtbl.add subst_id1 id2 subst (*;
                     Hashtbl.iter
                       (fun id rplc ->
                          Util.sysout 3 ((term_to_hotptp st.index.termbase id1)^" match "^(term_to_hotptp st.index.termbase id2)
                            ^": "^(term_to_hotptp st.index.termbase id)^" -> "^(term_to_hotptp st.index.termbase (rplc))^"\n"))
                     subst *)
                    )
                 )
               lits;
               if (Hashtbl.length subst_id1)>0 then Hashtbl.add substs id1 subst_id1
             )
           subsumes;

         (* output subsumptions *)
         (* Hashtbl.iter
           (fun id1 lits ->
            let lits = IdSet.remove id1 lits in
            let id1vars = varpoints st id1 [] in
            Util.sysout 3 ("  term "^(string_of_int id1)^":"^(term_to_hotptp st.index.termbase id1)^" subsumes \n");
            IdSet.iter
              (fun id2 ->
                 Util.sysout 3 ("  term "^(string_of_int id2)^":"^(term_to_hotptp st.index.termbase id2)^".\n");
                 Util.sysout 3 "  subst: [";
                 Hashtbl.iter
                   (fun id poslist -> Util.sysout 3 ((term_to_hotptp st.index.termbase id)^"/");
                                      List.iter
                                        (fun pos -> let id_sub = occurs_at pos id2 st.index in
                                                    if id != id_sub
                                                    then Util.sysout 3 ((term_to_hotptp st.index.termbase id_sub)^" "))
                                        poslist;
                                      Util.sysout 3 ","
                                      )
                 id1vars;
                 Util.sysout 3 "]\n")
              lits)
          subsumes *)
          Hashtbl.iter
            (fun id1 substs ->
               Hashtbl.iter
                 (fun id2 subst ->
                   Util.sysout 3 ("  term "^(string_of_int id1)^":"^(term_to_hotptp st.index.termbase id1)^" subsumes "
                   ^(string_of_int id2)^":"^(term_to_hotptp st.index.termbase id2)^" with substitution:\n  [");
                   let first = ref true in
                   Hashtbl.iter
                     (fun v rplc ->
                       if (not (!first)) then (Util.sysout 3 ",") else first := false; 
                       Util.sysout 3 ((term_to_hotptp st.index.termbase v)^"/"^(term_to_hotptp st.index.termbase rplc))
                     )
                     subst;
                   Util.sysout 3 "]\n"
                 )
                 substs
            )
            substs
         )
     clause_mods;
    
  []

(** Rename Free Variables in Clause *)

let rename_free_variables (cl:cl_clause) (st:state) =
  match cl.cl_free_vars with
    [] -> cl
  | free_vars -> 
      let new_free_vars = 
	List.map (fun var -> create_and_insert_new_free_var_with_simple_name (Term.type_of (type_of_symbol st.signature) var) st) free_vars in
      let substpairlist = 
	List.map2 (fun var1 var2 -> ((term2xterm var1),(term2xterm var2))) free_vars new_free_vars in
      let newlits = List.map (fun l -> substitute_lit l st substpairlist) (Array.to_list cl.cl_litarray) in
      mk_clause newlits (inc_clause_count st) new_free_vars ("rename",[(cl.cl_number,"")],"") cl.cl_origin st
   


(** The Resolution Rule *)

(* this function, which determines potential candiate specifications for resolution steps, should later be replaced by something more efficient using the index *)

let is_uni_lit (l:role lit_literal) =
  if l.lit_polarity then false else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),_,_),_,_) -> true
  | _ -> false

let has_uni_lit (cl:cl_clause) =
(*  List.exists is_uni_lit (Array.to_list cl.cl_litarray) *)
  false
      
let mk_res_combinations (i1:int) (i2:int) =
  Util.sysout 5 ("\n :mk_res_combinations: "^(string_of_int i1)^" "^(string_of_int i2));
  let rec help (h1:int) (h2:int) (accu:(int * int) list) =
    Util.sysout 5 ("\n  :help: "^(string_of_int i1)^" "^(string_of_int i2)^" "^(List.fold_left (fun s (a,b) -> (s^" ("^(string_of_int a)^","^(string_of_int b)^")")) "" accu));
    if h1 <= 0 && h2 <= 0 then ((h1,h2)::accu) else 
    if h1 <= 0 && h2 > 0 then help i1 (h2 - 1) ((h1,h2)::accu) else 
    help (h1 - 1) h2 ((h1,h2)::accu) in 
  let result = help i1 i2 [] in
    Util.sysout 5 ("\n :result: "^(List.fold_left (fun s (a,b) -> (s^" ("^(string_of_int a)^","^(string_of_int b)^")")) "" result));
    result
    
  
let rem_from_array_to_list (a:'a array) (i:int) =
  if (i<0) || (i>=(Array.length a)) then raise (Failure "remove_from_array_to_list")
  else
    let subl1 = 
      if i = 0 then [] 
      else (Array.to_list (Array.sub a 0 i))
    and subl2 = 
      if i = (Array.length a) then [] 
      else (Array.to_list (Array.sub a (i+1) ((Array.length a)-(i+1))))
    in
    subl1@subl2

let have_common_free_variables (cl1:cl_clause) (cl2:cl_clause) =
  (List.exists (fun v1 -> (List.exists (fun v2 -> v1 = v2) cl2.cl_free_vars)) cl2.cl_free_vars)

let resolve (cl1:cl_clause) (cl2:cl_clause) (st:state) =
(*  match (cl1.cl_origin,cl2.cl_origin,st.flags.sos) with
      (AXIOM,AXIOM,true) -> []
    | _ -> 
*)
	let res (cl1:cl_clause) (i1:int) (cl2:cl_clause) (i2:int) (st:state) =
	  Util.sysout 5 ("\n res "^(string_of_int cl1.cl_number)^" "^(string_of_int i1)^" "^(string_of_int cl2.cl_number)^" "^(string_of_int i2));
	  let l1 = (Array.get cl1.cl_litarray i1) and l2 = (Array.get cl2.cl_litarray i2) in
	  let t1 = lit_term l1 and p1 = lit_polarity l1 and 	
	      t2 = lit_term l2 and p2 = lit_polarity l2 in
	    if p1 = p2 then [] else
	      let rl1 = rem_from_array_to_list cl1.cl_litarray i1     
	      and	rl2 = rem_from_array_to_list cl2.cl_litarray i2  
	      in 
	      let neworigin =  
		(* if cl1.cl_origin = CONJECTURE & cl2.cl_origin = CONJECTURE then CONJECTURE else DERIVED in *)
                DERIVED
              in
	      let newlit = lit_mk_uni_literal st.signature t1 t2 "" in
		[mk_clause 
		   (newlit::(List.merge lit_compare rl1 rl2)) 
		   (inc_clause_count st) 
		   (cl1.cl_free_vars@cl2.cl_free_vars) 
		   ("res",[(cl1.cl_number,"");(cl2.cl_number,"")],"")
		   neworigin
		   st
		]
	in 
	  (*  if has_uni_lit cl1 || has_uni_lit cl2 then []  else *)
    (*
	    let cl2_copy = 
	    if have_common_free_variables cl1 cl2
	    then rename_free_variables cl2 st
	    else cl2
	    in
    *)
	  (* let cl1_renamed = rename_free_variables cl1 st in *)
	(* let res_lit_pairs = mk_res_combinations (cl1.cl_max_lit_num - 1) (cl2_copy.cl_max_lit_num - 1) *)
	let res_lit_pairs = mk_res_combinations ((List.length (Array.to_list cl1.cl_litarray)) - 1) ((List.length (Array.to_list cl2.cl_litarray)) - 1) 
	in List.fold_right (fun (l1,l2) l -> ((res cl1 l1 cl2 l2 st)@l)) res_lit_pairs [] 

  

(** The Restricted Factorization Rule (only two literals, but extensional) *)

(*
let factorize_restricted (cl:cl_clause) (st:state) =
  Util.sysout 0 ("\n\  FACTORIZE-RESTRICTED: "^(cl_clause_to_protocol cl));
  let litlist = (Array.to_list cl.cl_litarray) in
  let result = 
    match litlist with
       l1::l2::[] -> 
	   let t1 = lit_term l1 and p1 = lit_polarity l1 and 	
	       t2 = lit_term l2 and p2 = lit_polarity l2 in
	   if p1 = p2 
	   then 
	     let newlit = lit_mk_uni_literal t1 t2 "" in
	     let keeplit = if is_flex_lit l1 then l1 else l2 in
               [mk_clause [keeplit;newlit]
		 (inc_clause_count st) 
		 (cl.cl_free_vars) 
		 ("fac_restr",[(cl.cl_number,"")],"")
		 cl.cl_origin st]
	   else
	     if (not (p1 = p2)) 
	     then
	       (
		if is_flex_lit l1 
		then
		  let t2 = (xterm2term l2.lit_term) in 
		  let negt2 = Appl(Symbol "~",t2) in
		  let newlit = lit_mk_uni_literal t1 (term2xterm negt2)  "" in
		  [mk_clause [l1;newlit]
		     (inc_clause_count st) 
		     (cl.cl_free_vars) 
		     ("fac_restr",[(cl.cl_number,"")],"")
		     cl.cl_origin st]
		else 
		  if is_flex_lit l2 
		  then let t1 = (xterm2term l1.lit_term) in 
		  let negt1 = Appl(Symbol "~",t1) in
		  let newlit = lit_mk_uni_literal t2 (term2xterm negt1) "" in
		  [mk_clause [l2;newlit]
		     (inc_clause_count st) 
		     (cl.cl_free_vars) 
		     ("fac_restr",[(cl.cl_number,"")],"")
		     cl.cl_origin st]
		  else [])
	     else []
     | _ -> [] 
  in 
    Util.sysout 0 ("  FACTORIZE-RESTRICTED-RESULT: "^(cl_clauselist_to_protocol result)^"\n");
    result
*)



let factorize_restricted (cl:cl_clause) (st:state) =
  Util.sysout 3 ("\n\  FACTORIZE-RESTRICTED: "^(cl_clause_to_protocol cl));
  let litlist = (Array.to_list cl.cl_litarray) in
  let result = 
    match litlist with
       l1::l2::[] -> 
	   let t1 = lit_term l1 and p1 = lit_polarity l1 and 	
	       t2 = lit_term l2 and p2 = lit_polarity l2 in
	   if p1 = p2 
	   then 
	     let newlit = lit_mk_uni_literal st.signature t1 t2 "" in
	     let keeplit = if is_flex_lit l1 then l1 else l2 in
              [mk_clause [keeplit;newlit]
		 (inc_clause_count st) 
		 (cl.cl_free_vars) 
		 ("fac_restr",[(cl.cl_number,"")],"")
		 cl.cl_origin st]
	   else
	     if (not (p1 = p2)) 
	     then
	       (
		if is_flex_lit l1 
		then
		  let t2 = (xterm2term l2.lit_term) in 
		  let negt2 = Appl(Symbol "~",t2) in
		  let newlit = lit_mk_uni_literal st.signature t1 (term2xterm negt2)  "" in
		  [mk_clause [l1;newlit]
		     (inc_clause_count st) 
		     (cl.cl_free_vars) 
		     ("fac_restr",[(cl.cl_number,"")],"")
		     cl.cl_origin st]
		else 
		  if is_flex_lit l2 
		  then let t1 = (xterm2term l1.lit_term) in 
		  let negt1 = Appl(Symbol "~",t1) in
		  let newlit = lit_mk_uni_literal st.signature t2 (term2xterm negt1) "" in
		  [mk_clause [l2;newlit]
		     (inc_clause_count st) 
		     (cl.cl_free_vars) 
		     ("fac_restr",[(cl.cl_number,"")],"")
		     cl.cl_origin st]
		  else [])
	     else []
     | _ -> [] 
  in 
    Util.sysout 3 ("  FACTORIZE-RESTRICTED-RESULT: "^(cl_clauselist_to_protocol result)^"\n");
    result


(* double result rule --- leads to probelsm e.g. with CANTOR
let factorize_restricted (cl:cl_clause) (st:state) =
  Util.sysout 3 ("\n\  FACTORIZE-RESTRICTED: "^(cl_clause_to_protocol cl));
  let litlist = (Array.to_list cl.cl_litarray) in
  let result = 
    match litlist with
       l1::l2::[] -> 
	   let t1 = lit_term l1 and p1 = lit_polarity l1 and 	
	       t2 = lit_term l2 and p2 = lit_polarity l2 in
	   if p1 = p2 
	   then 
	     let newlit = lit_mk_uni_literal t1 t2 "" in
               [mk_clause [l1;newlit] (inc_clause_count st) (cl.cl_free_vars) 
		 ("fac_restr",[(cl.cl_number,"")],"") cl.cl_origin st;
		mk_clause [l2;newlit] (inc_clause_count st) (cl.cl_free_vars) 
		 ("fac_restr",[(cl.cl_number,"")],"") cl.cl_origin st]
	   else
	     if (not (p1 = p2)) 
	     then
	       let t1 = (xterm2term l1.lit_term) in 
	       let negt1 = Appl(Symbol "~",t1) in
	       let newlit = lit_mk_uni_literal t2 (term2xterm negt1) "" in
		 [mk_clause [l1;newlit] (inc_clause_count st) (cl.cl_free_vars) 
		    ("fac_restr",[(cl.cl_number,"")],"") cl.cl_origin st;
		  mk_clause [l2;newlit] (inc_clause_count st) (cl.cl_free_vars) 
		    ("fac_restr",[(cl.cl_number,"")],"") cl.cl_origin st]
	     else []
     | _ -> [] 
  in 
    Util.sysout 3 ("\n  FACTORIZE-RESTRICTED-RESULT: "^(cl_clauselist_to_protocol result)^"\n");
    result
*)


(* Here is a more general version for factorize_restricted --- but that kills problems like TPTP-v3.7.0/THF/LCL600^1.p 

let mk_fac_combinations (i1:int) =
  let result = ref [] in  
    for a = 0 to i1 do
      for b = 0 to i1 do
	if a != b && (not (List.mem (b,a) !result)) then result := (a,b)::!result 
      done
    done;
    !result
    
  
let factorize_restricted (cl:cl_clause) (st:state) =
  let fac (cl:cl_clause) (i1:int) (i2:int) (st:state) =
    let l1 = (Array.get cl.cl_litarray i1) and l2 = (Array.get cl.cl_litarray i2) in
    let t1 = lit_term l1 and p1 = lit_polarity l1 and 	
	t2 = lit_term l2 and p2 = lit_polarity l2 in
    if p1 = p2 
      (* && (get_head t1) = (get_head t2) *)
    then
      let rl = rem_from_array_to_list cl.cl_litarray i1     
      in 
      let newlit = lit_mk_uni_literal t1 t2 "" in
	[mk_clause 
	   (newlit::rl)
	   (inc_clause_count st) 
	   cl.cl_free_vars
	   ("fac_restr",[(cl.cl_number,"")],"")
	   st
	]
    else (*  p1 != p2 *)
      let rl = rem_from_array_to_list cl.cl_litarray i1 in
      let tt2 = (xterm2term t2) in 
      let negtt2 = Appl(Symbol "~",tt2) in
      let newlit = lit_mk_uni_literal t1 (term2xterm negtt2)  "" in  
	[mk_clause 
	   (newlit::rl)
	   (inc_clause_count st) 
	   cl.cl_free_vars
	   ("fac_restr",[(cl.cl_number,"")],"")
	   st
	]
  in 
  let fac_lit_pairs = mk_fac_combinations (cl.cl_max_lit_num - 1)
  in List.fold_right (fun (i1,i2) l -> ((fac cl i1 i2 st)@l)) fac_lit_pairs [] 

*)


(** The Simplification Rule *)

(* this does not do much yet !!! *)
let simplify (cl:cl_clause) (st:state) =
  (* output st (fun () -> ("\n\  SIMPLIFY: "^(cl_clause_to_protocol cl))); *)
  let rec faclits (ll:role lit_literal list) (flag2:bool) (rl:role lit_literal list) =
    match ll with 
      [] -> (flag2,rl)
    | hd::tl -> 
	if List.exists 
	    (fun lit -> 
	      lit.lit_polarity = hd.lit_polarity
		&& 
	      (xterm2term lit.lit_term) = (xterm2term hd.lit_term) 
		)
	    tl 
	then faclits tl (true || flag2) rl else faclits tl flag2 (hd::rl)  in
  let larray = cl.cl_litarray in
  let newlits = ref [] 
  and tautology = ref false 
  and flag1 = ref false in
  for i = 0 to ((Array.length larray) - 1) do
    let lit = larray.(i) in
    (* make this more efficient *)
    if List.exists (fun l -> 
	              (not (lit.lit_polarity = l.lit_polarity))
		      &&	        
	             (xterm2term lit.lit_term) = (xterm2term l.lit_term) 
		    )
                    !newlits
    then tautology := true
    else 
     match (xterm2term lit.lit_term) with
     | Symbol "$true" -> 
	 if lit.lit_polarity then tautology := true
	 else flag1 := true
     | Symbol "$false" -> 
	 if lit.lit_polarity then flag1 := true
	 else tautology := true
     | Appl(Appl((Symbol "="),t1),t2) ->
	 if (t1 = t2) then  
	   if lit.lit_polarity then tautology := true 
	   else flag1 := true
	 else newlits := lit::(!newlits)
     | _ -> newlits := lit::(!newlits)
  done;
  if !tautology then []
  else 
    let (poslits,neglits) = List.partition  (fun l -> l.lit_polarity) (Array.to_list cl.cl_litarray) in
    if List.exists (fun l1 -> List.exists (fun l2 -> l1.lit_term = l2.lit_term) neglits) poslits 
    then []
    else 
      let (flag2,newlits2) = faclits !newlits false [] in
      let result = 
	if (!flag1 || flag2) 
	then
	  ( 
	    [mk_clause 
	       newlits2
	       (inc_clause_count st) 
	       (cl.cl_free_vars) 
	       ("sim",[(cl.cl_number,"")],"")
	       cl.cl_origin st]
	   )
	else [cl] in
      (* output st (fun () -> ("  SIMPLIFY-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); *)
      result



(** The Trivial Unification Rule *)

let triv_lit (l:role lit_literal) (st:state) =
  if l.lit_polarity then (false,[l]) else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
      if (im2xterm l1) = (im2xterm l2) then (true,[]) else (false,[l])	
  | _ -> (false,[l])

let trivial (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  TRIVIAL: "^(cl_clause_to_protocol cl))); 
  let (flag,newlits) = 
    List.fold_right 
      (fun l (b,ll) -> let (nb,nll) = triv_lit l st in (b || nb,ll@nll))
      (Array.to_list cl.cl_litarray)
      (false,[])
  in 
  let result =
    if flag then 
      [mk_clause newlits (inc_clause_count st) 
	 (cl.cl_free_vars) ("triv",[(cl.cl_number,"")],"") cl.cl_origin st]
    else [] in
  output st (fun () -> ("  TRIVIAL-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); 
  result


(** The Boolean Extensionality Rule *)

let bool_lit (l:role lit_literal) (st:state)=
  if l.lit_polarity || (not ((l.lit_info = "dec") || (l.lit_info = "func"))) 
     (* bool is only applied if previously dec or func has been applied *)
  then (false,[l],[l]) else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
      (
       if  (type_of (im2xterm l1)) = bt_o  
	   (* is_basetype (type_of (im2xterm l1)) *)
       then 
	 (true,
	  [(lit_mk_neg_literal st.signature (im2xterm l1)); 
	   (lit_mk_neg_literal st.signature (im2xterm l2))],
	  [(lit_mk_pos_literal st.signature (im2xterm l1)); 
	   (lit_mk_pos_literal st.signature (im2xterm l2))]
	 ) 
       else (false,[l],[l])
      )
   | _ -> (false,[l],[l])



let bool_pos_lit (l:role lit_literal) (st:state)=
  match (xterm2im l.lit_term 3) with
     Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
       (
	if 
          (type_of (im2xterm l1)) = bt_o
	then 
	  if l.lit_polarity
	  then	
	    (true,
	     [(lit_mk_neg_literal st.signature (im2xterm l1));
	      (lit_mk_pos_literal st.signature (im2xterm l2))],
	     [(lit_mk_pos_literal st.signature (im2xterm l1));
	      (lit_mk_neg_literal st.signature (im2xterm l2))]
	    )
	  else
	    (false,[l],[l])
	else (false,[l],[l])
       )
   | _ -> (false,[l],[l])
	 


let boolean_ext (cl:cl_clause) (st:state) =
  let (flag,newlits1,newlits2) = 
    List.fold_right 
      (fun l (b,ll1,ll2) -> let (nb,nll1,nll2) = bool_lit l st in (b || nb,ll1@nll1,ll2@nll2))
      (Array.to_list cl.cl_litarray)
      (false,[],[])
  in
(* 
   output_debug "\n Index based (roles not implemented yet):\n";
   List.iter
   (fun t -> output_debug ((Term.to_string (Termset.retrieve st.index.termbase t))^"\n"))
   (* this is the list of all terms with headsymbol "=": *)
   (Hashtbl.find_all (st.index).has_headsymbol (Termset.create st.index.termbase (Symbol "=")));
   (* refinements to do:
      - restriction to literals (index_with_role)
      - indexing of symbol occurrences at given positions *)
   output_debug "\n First try on roles:\n";
   if ((Hashtbl.mem st.index.term_at_pos_role [Function;Function]) &&
   (Hashtbl.mem (Hashtbl.find st.index.term_at_pos_role [Function;Function]) (Termset.create st.index.termbase (Symbol "=")))) then 
   IdSet.iter
   (fun t -> output_debug ((Term.to_string (Termset.retrieve st.index.termbase t)^"\n")))
   (* this is the list of all literals that are equations: *)
   (Hashtbl.find (Hashtbl.find st.index.term_at_pos_role [Function;Function]) (Termset.create st.index.termbase (Symbol  "=")))
   else
   output_debug "nothing suitable found.\n";
*)
  if flag then     
    [(mk_clause newlits1 (inc_clause_count st) 
	(cl.cl_free_vars) ("extcnf_equal_neg",[(cl.cl_number,"")],"") cl.cl_origin st);
     (mk_clause newlits2 (inc_clause_count st) 
	(cl.cl_free_vars) ("extcnf_equal_neg",[(cl.cl_number,"")],"") cl.cl_origin st)]
  else []  (* do not pass cl on *)



let boolean_ext_pos (cl:cl_clause) (st:state) =
  let (flag,newlits1,newlits2) = 
    List.fold_right 
      (fun l (b,ll1,ll2) -> let (nb,nll1,nll2) = bool_pos_lit l st in (b || nb,ll1@nll1,ll2@nll2))
      (Array.to_list cl.cl_litarray)
      (false,[],[])
  in
  if flag then     
    [(mk_clause newlits1 (inc_clause_count st) 
	(cl.cl_free_vars) ("extcnf_equal_pos",[(cl.cl_number,"")],"") cl.cl_origin st);
     (mk_clause newlits2 (inc_clause_count st) 
	(cl.cl_free_vars) ("extcnf_equal_pos",[(cl.cl_number,"")],"") cl.cl_origin st)]
  else [cl] (* need to pass cl for pre_processing_1 *)



let boolean_ext_pos_main_loop (cl:cl_clause) (st:state) =  
  let count = st.clause_count in 
  let result = boolean_ext_pos cl st in
    if count < st.clause_count 
    then result
    else []
 



(** The Functional Extensionality Rule *)

let func_terms (t1:term) (t2:term) (ty:hol_type) (st:state) (free_vars:term list) =
  let fv_type_list = List.map (fun v -> type_of_symbol st.signature (get_symbol v)) free_vars in
  let sk_const_ty = List.fold_right (fun l1 l2 -> abstr_type l1 l2) fv_type_list ty in
  let skoconst = create_and_insert_skolem_const (Symbol "E") sk_const_ty st in
  let skoterm =  List.fold_left (fun l1 l2 -> Appl(l1,l2)) skoconst free_vars 
  in
  ((beta_normalize (Appl(t1,skoterm))),(beta_normalize (Appl(t2,skoterm))))

let func_terms_pos (t1:term) (t2:term) (ty:hol_type) (st:state) =
  let newvar = create_and_insert_new_free_var (Symbol "E") ty st 
  in
  ((beta_normalize (Appl(t1,newvar))),(beta_normalize (Appl(t2,newvar))),newvar)

let func_lit (l:role lit_literal) (cl:cl_clause) (st:state)=
  if l.lit_polarity then (false,[l]) else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
      let ty = (type_of (im2xterm l1)) in
      (
       if is_funtype ty  (* klappt noch nicht; type is still X0 *)
       then 
	 let arg_ty = arg_type ty and
	     nt1 = (im2term l1) and nt2 = (im2term l2) in
	 let (sk_1,sk_2) = func_terms nt1 nt2 arg_ty st cl.cl_free_vars in
	 (true,[lit_mk_uni_literal st.signature (term2xterm sk_1) (term2xterm sk_2) "func"])
       else
	 (false,[l])
      )
  | _ -> (false,[l])

let func_lit_pos (l:role lit_literal) (cl:cl_clause) (st:state)=
  if (not l.lit_polarity) then (false,[l],[]) else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
      let ty = (type_of (im2xterm l1)) in
      (
       if is_funtype ty  (* klappt noch nicht; type is still X0 *)
       then 
	 (
	  let arg_ty = arg_type ty and
	      nt1 = (im2term l1) and nt2 = (im2term l2) in
	  let (sk_1,sk_2,newvar) = func_terms_pos nt1 nt2 arg_ty st in
	  (true,[lit_mk_eq_literal st.signature (term2xterm sk_1) (term2xterm sk_2) "func"],[newvar])
	 )
       else
	 (
	  (false,[l],[])
	 )
      )
  | _ -> (false,[l],[])

let functional_ext (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  FUNCTIONAL-EXT: "^(cl_clause_to_protocol cl))); 
  let (flag,newlits) = 
    List.fold_right 
      (fun l (b,ll) -> let (nb,nll) = func_lit l cl st in (b || nb,ll@nll))
      (Array.to_list cl.cl_litarray)
      (false,[])
  in 
  let result =
    if flag then     
      [mk_clause newlits (inc_clause_count st) 
	 (cl.cl_free_vars) ("extcnf_equal_neg",[(cl.cl_number,"")],"") cl.cl_origin st]
    else [] in
  output st (fun () -> ("  FUNCTIONAL-EXT-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); 
  result


let functional_ext_pos (cl:cl_clause) (st:state) =
  let (flag,newlits,newfreevars) = 
    List.fold_right 
      (fun l (b,ll,fvl) -> let (nb,nll,nfvl) = func_lit_pos l cl st in (b || nb,ll@nll,fvl@nfvl))
      (Array.to_list cl.cl_litarray)
      (false,[],cl.cl_free_vars)
  in 
  if flag then     
    [mk_clause newlits (inc_clause_count st) 
	newfreevars ("extcnf_equal_pos",[(cl.cl_number,"")],"") cl.cl_origin st]
  else [cl]

(*
let functional_ext_exhaustively (cl:cl_clause) (st:state) =
  let rec functional_ext_exhaustively_help (cll:cl_clause list) (st:state) (accu:cl_clause list) =
    match cll with
       [] -> accu
     | hd::tl -> 
	 let count = st.clause_count in 
	 let rl = functional_ext hd st in
	 if count >= st.clause_count (* termination *) 
	 then functional_ext_exhaustively_help tl st (rl@accu)
	 else functional_ext_exhaustively_help (rl@tl) st accu
  in
  functional_ext_exhaustively_help [cl] st []

let functional_ext_pos_exhaustively (cl:cl_clause) (st:state) =
  let rec functional_ext_pos_exhaustively_help (cll:cl_clause list) (st:state) (accu:cl_clause list) =
    match cll with
       [] -> accu
     | hd::tl -> 
	 let count = st.clause_count in 
	 let rl = functional_ext_pos hd st in
	 if count >= st.clause_count (* termination *) 
	 then functional_ext_pos_exhaustively_help tl st (rl@accu)
	 else functional_ext_pos_exhaustively_help (rl@tl) st accu
  in
  functional_ext_pos_exhaustively_help [cl] st []
*)



(** The Functional Unification Rule (same as Functional Extensionality Rule except for the new terms) *)

let func_uni_terms (t1:term) (t2:term) (ty:hol_type) (st:state) =
  let skoconst = create_and_insert_skolem_const (Symbol "E") ty st in
  ((beta_normalize (Appl(t1,skoconst))),(beta_normalize (Appl(t2,skoconst))))


let func_uni_lit (l:role lit_literal) (cl:cl_clause) (st:state)=
  if l.lit_polarity then (false,[l]) else
  match (xterm2im l.lit_term 3) with
    Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> 
      let ty = (type_of (im2xterm l1)) in
      (
       if is_funtype ty  
       then 
	 let arg_ty = arg_type ty and
	     nt1 = (im2term l1) and nt2 = (im2term l2) in
	 let (sk_1,sk_2) = func_uni_terms nt1 nt2 arg_ty st in
	 (true,[lit_mk_uni_literal st.signature (term2xterm sk_1) (term2xterm sk_2) "func_uni"])
       else
	 (false,[l])
      )
  | _ -> (false,[l])

let func_uni (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  FUNCTIONAL-UNI: "^(cl_clause_to_protocol cl))); 
  let (flag,newlits) = 
    List.fold_right 
      (fun l (b,ll) -> let (nb,nll) = func_uni_lit l cl st in (b || nb,ll@nll))
      (Array.to_list cl.cl_litarray)
      (false,[])
  in 
  let result =
    if flag then     
      [mk_clause newlits (inc_clause_count st) 
	 (cl.cl_free_vars) ("func_uni",[(cl.cl_number,"")],"") cl.cl_origin st]
    else [] in
  output st (fun () -> ("  FUNCTIONAL-UNI-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); 
  result


(** The Flex-Rigid Rule *)


let rec mk_multi_appl (head:term)  (termlist:term list) = 
    match termlist with
      [] -> head
    | hd::tl -> mk_multi_appl (Appl(head,hd)) tl

let rec mk_multi_abstr (vartypelist:(term * hol_type) list) (body:term) = 
  match vartypelist with
    [] -> body
  | (v,ty)::tl -> Abstr(v,ty,(mk_multi_abstr tl body)) 


let imi_binding (hd1:term)  (arg_tys1:hol_type list) (ty1:hol_type) (hd2:term) (arg_tys2:hol_type list) (ty2:hol_type) (st:state) =
  output st (fun () -> ("\n\  ENTER IMI-BINDING: "^(Term.to_string hd1)^" "^(Hol_type.to_hotptp ty1)^" "^(Term.to_string hd2)^" ["^(List.fold_left (fun s i -> (s^" "^(Hol_type.to_hotptp i))) "" arg_tys2)^"]"));
  Util.sysout 3 ("\n\  ENTER IMI-BINDING: "^(Term.to_string hd1)^" "^(Hol_type.to_hotptp ty1)^" "^(Term.to_string hd2)^" ["^(List.fold_left (fun s i -> (s^" "^(Hol_type.to_hotptp i))) "" arg_tys2)^"] "^(Hol_type.to_hotptp ty2));
  assert (ty1 = ty2);
  let new_vars = 
    List.map (fun ty -> create_and_insert_new_free_var_with_simple_name ty st) arg_tys1 in
(*  Util.sysout 3 "\n new_vars: "; List.iter (fun x -> (Util.sysout 3 (Term.to_hotptp x))) new_vars; *)
  let new_head_vars = 
    List.map (fun ty -> create_and_insert_new_free_var_with_simple_name (mk_funtype arg_tys1 ty) st) arg_tys2 in
(*  Util.sysout 3 "\n new_head_vars: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) new_head_vars; *)
  let new_arg_terms =
    List.map (fun head -> mk_multi_appl head new_vars) new_head_vars in 
(*  Util.sysout 3 "\n new_arg_terms: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) new_arg_terms; *)
  let new_compound_term = mk_multi_appl hd2 new_arg_terms in
(*  (Util.sysout 3 ("\n new_compound_term: "^(Term.to_hotptp new_compound_term))); *)
  let result = mk_multi_abstr (List.combine new_vars arg_tys1) new_compound_term in
  output st (fun () -> ("\n\  LEAVE IMI-BINDING: "));
  beta_normalize result
	
let proj_bindings (hd:term)  (arg_tys:hol_type list) (ty:hol_type) (st:state) =
  output st (fun () -> ("\n\  ENTER PROJ-BINDING: "^(Term.to_string hd)^" ["^(List.fold_left (fun s i -> (s^" "^(Hol_type.to_hotptp i))) "" arg_tys)^"]"^" "^(Hol_type.to_hotptp ty)));
  output st (fun () -> ("\n\  ENTER PROJ-BINDING: "));
  let new_vars = 
    List.map (fun ty -> create_and_insert_new_free_var_with_simple_name ty st) arg_tys in
(*  Util.sysout 3 "\n new_vars: ";  List.iter (fun x -> (Util.sysout 3 (Term.to_hotptp x))) new_vars; *)
 let result =
   List.flatten
     (List.map 
	(fun proj_var -> 
	  let proj_var_ty = Term.type_of (type_of_symbol st.signature) proj_var in
(*       Util.sysout 3 ("\n proj_var_ty: "^(Hol_type.to_string proj_var_ty)); *)
	  let (flag,proj_var_arg_tys) = all_arg_types_up_to_goal_type proj_var_ty ty in
(*       Util.sysout 3 "\n proj_var_arg_tys:"; List.iter (fun x -> (Util.sysout 3 ((Hol_type.to_string x)^" "))) proj_var_arg_tys; *)
	  if (not flag) then []
	  else
	    let new_head_vars = 
	      List.map (fun ty -> create_and_insert_new_free_var_with_simple_name  (mk_funtype arg_tys ty) st) proj_var_arg_tys in
(*           Util.sysout 3 "\n new_head_vars: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) new_head_vars; *)
	    let new_arg_terms =
	      List.map (fun head -> mk_multi_appl head new_vars) new_head_vars in 
(*           Util.sysout 3 "\n new_arg_terms: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) new_arg_terms; *)
	    let new_compound_term = mk_multi_appl proj_var new_arg_terms in
(*           Util.sysout 3 ("\n new_compound_term: "^(Term.to_hotptp new_compound_term)); *)
	    [mk_multi_abstr (List.combine new_vars arg_tys) new_compound_term])
	new_vars) in
 output st (fun () -> ("\n\  LEAVE PROJ-BINDING: "));
 result

let eq_bindings (arg_tys1:hol_type list) (st:state) =
    match arg_tys1 with
      [ty1;ty2] -> 
	if (ty1 = ty2) 
	then 
	  let new_vars = 
	   [create_and_insert_new_free_var_with_simple_name ty1 st;
	    create_and_insert_new_free_var_with_simple_name ty2 st] in
	  let new_compound_term_1 = mk_multi_appl (get_defined_symbol st.signature nequals) new_vars
	  and new_compound_term_2 = mk_multi_appl (Symbol equality) new_vars in
	  let result_1 = (beta_normalize (mk_multi_abstr (List.combine new_vars arg_tys1) new_compound_term_1)) 
	  and result_2 = (beta_normalize (mk_multi_abstr (List.combine new_vars arg_tys1) new_compound_term_2)) in
	    [result_1;result_2]
	else []
    | _ -> []

let eq_binding (arg_ty:hol_type) (st:state) =
  let new_vars = 
	   [create_and_insert_new_free_var_with_simple_name arg_ty st;
	    create_and_insert_new_free_var_with_simple_name arg_ty st] in
  let new_compound_term = mk_multi_appl (Symbol equality) new_vars in
  let result = (beta_normalize (mk_multi_abstr (List.combine new_vars [arg_ty;arg_ty]) new_compound_term))  in
  result


let special_eq_imi_binding (arg_tys1:hol_type list) (arg_term:term) (st:state) =
   match arg_tys1 with
      [ty1] -> 
	let ty2 = Term.type_of (type_of_symbol st.signature) arg_term in
	  if ty1 = ty2 
	  then
	    let var1 = create_and_insert_new_free_var_with_simple_name ty1 st in
	    let term = mk_multi_appl (Symbol equality) [var1;arg_term] in
	    let result = mk_multi_abstr [(var1,ty1)] term in
	      [result]
	  else []
     | _ -> [] 
	 
	    

let flex_rigid_lit (l:role lit_literal) (st:state) =
  if l.lit_polarity then (false,[]) else
  match (xterm2term l.lit_term) with
    Appl(Appl((Symbol "="),t1),t2) -> 
      let ty1 = (Term.type_of (type_of_symbol st.signature) t1)
      and ty2 = (Term.type_of (type_of_symbol st.signature) t2) in
      let hd1 = Term.get_head_symbol t1 
      and hd2 = Term.get_head_symbol t2 in
(*    Util.sysout 3 ("\n hd1: "^(Term.to_string hd1)); *)
(*    Util.sysout 3 ("\n hd2: "^(Term.to_string hd2)); *)
      let ty_hd1 = Term.type_of (type_of_symbol st.signature) hd1
      and ty_hd2 = Term.type_of (type_of_symbol st.signature) hd2 in
(*    Util.sysout 3 ("\n ty_hd1: "^(Hol_type.to_string ty_hd1)); *)
(*    Util.sysout 3 ("\n ty_hd2: "^(Hol_type.to_string ty_hd2)); *)
      let (flag1,arg_tys_l1) = (types_of_all_arg_terms_up_to_term t1 hd1 (type_of_symbol st.signature))
(* (all_arg_types_up_to_goal_type ty_hd1 ty1) *)
      and (flag2,arg_tys_l2) = (types_of_all_arg_terms_up_to_term t2 hd2 (type_of_symbol st.signature))
(* (all_arg_types_up_to_goal_type ty_hd2 ty2) *)
      in
(*    Util.sysout 3 "\n arg_tys_1:"; List.iter (fun x -> (Util.sysout 3 ((Hol_type.to_string x)^" "))) arg_tys_l1; *)
(*    Util.sysout 3 "\n arg_tys_2:"; List.iter (fun x -> (Util.sysout 3 ((Hol_type.to_string x)^" "))) arg_tys_l2; *)
      if (Term.is_variable hd1) && (not (Term.is_variable hd2)) && (not (is_basetype ty_hd1)) && flag1 && flag2
      then 
	(true,
	 List.map (fun binding -> ((term2xterm hd1),(term2xterm binding)))
	   ((imi_binding hd1 arg_tys_l1 ty1 hd2 arg_tys_l2 ty2 st)::(proj_bindings hd1 arg_tys_l1 ty1 st)))
      else 
	if (not (Term.is_variable hd1)) && (Term.is_variable hd2) && (not (is_basetype ty_hd2)) && flag1 && flag2
	then 
	  (true,
	   List.map (fun binding -> ((term2xterm hd2),(term2xterm binding)))
	     ((imi_binding hd2 arg_tys_l2 ty2 hd1 arg_tys_l1 ty1 st)::(proj_bindings hd2 arg_tys_l2 ty2 st)))
	else	(false,[]) (* flex-flex-case *)   
   | _ -> (false,[])

let rec flex_rigid_first_lit (ll:(role lit_literal) list) (st:state) =
  match ll with
    [] -> (false,[])
  | hd::tl -> 
      let (flag,subst_pairs) = flex_rigid_lit hd st in
      if flag then (flag,subst_pairs) else flex_rigid_first_lit tl st

let flex_rigid (cl:cl_clause) (st:state) =
  output st (fun () -> ("\n\  FLEX-RIGID: "^(cl_clause_to_protocol cl))); 
  let litlist = (Array.to_list cl.cl_litarray) in
  let (flag,subst_pairs) = flex_rigid_first_lit litlist st in
  let result =
    if flag 
    then 
      (List.map 
	 (fun (var,gb) -> 
	   let newlits = List.map (fun l -> substitute_lit l st  [(var,gb)]) litlist
	   in
	   let new_free_vars = (litlist_free_vars newlits) in
	   mk_clause newlits (inc_clause_count st) new_free_vars 
	     ("flex_rigid",[(cl.cl_number, "[bind(" ^ to_string var ^ ", $thf(" ^ to_hotptp gb ^ "))]")], "") cl.cl_origin st)
	 subst_pairs)
    else [] in
  output st (fun () -> ("  FLEX-RIGID-RESULT: "^(cl_clauselist_to_protocol result)^"\n")); 
  result




(** The Primsubst Rule *)



let prim_subst (cl:cl_clause) (st:state) =
  let find_prim_subst_vars litlist =
    List.flatten 
      (List.map 
	 (fun l -> 
	    assert (not (is_abstr l.lit_term));
	    let hd = get_head_symbol l.lit_term in
	      if is_variable hd then [xterm2term hd] else [])
	 litlist) 
  in
(*
  let find_prim_subst_vars_and_args litlist =
    List.flatten 
      (List.map 
	 (fun l -> 
	   match xterm2term l.lit_term with
	       Appl(t1,t2) -> 
		 if Term.is_variable t1 then [(t1,t2)] else []
	     | _ -> [])
	 litlist)
  in
*)
(*  let leibniz_eq_heads_and_argterms litlist =
    let (poslits,neglits) = (List.partition (fun l -> l.lit_polarity) litlist) in
    let posheads = find_prim_subst_vars poslits 
    and	negheads_and_args = find_prim_subst_vars_and_args neglits in
      List.filter (fun (x,_) -> List.mem x posheads) negheads_and_args
  in
*)
  let litlist = (Array.to_list cl.cl_litarray) in
  let varlist = find_prim_subst_vars litlist in
  let normal_results =
    match varlist with
	[] -> []
      | _ ->
	  (List.flatten
	     (List.map
		(fun var -> 
		   let xvar = term2xterm var in
		   let var_ty = Term.type_of (type_of_symbol st.signature) var in
		   let var_goal_ty = base_result_type var_ty in
		   let (flag,var_arg_tys) = all_arg_types_up_to_goal_type var_ty var_goal_ty in
		     assert flag;
		     let prim_subst_pairs = 

		       let base_1 =			 
			   [
			     (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol ctrue) [] bt_o st));
			     (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol cfalse) [] bt_o st));
			     (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol neg) [bt_o] bt_o st))
                           ] in

		       let eq_bindings = (eq_bindings var_arg_tys st) in
		       let special_eq_imi_bindings =  
			 (List.flatten 
			    (List.map (fun (string,tp) -> 
					 (special_eq_imi_binding var_arg_tys (Symbol string) st)) 
			       (List.filter (fun (str,tp) -> 
					       (not (Term.is_variable (Symbol str)))) 
				  (all_uninterpreted_symbols st.signature)))) in
		       let base_2 = 
			 (List.map (fun term -> (xvar,term2xterm term)) (eq_bindings@special_eq_imi_bindings)) in
				      
		       let base_3 =
			   [
			     (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol disjunction) [bt_o;bt_o] bt_o st));
			     (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol equality) [bt_i;bt_i] bt_o st))
			   ]
			 @ (List.map (fun b -> (term2xterm var,term2xterm b)) (proj_bindings var var_arg_tys var_goal_ty st)) in

		       let base_4 =
			     [
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol forall) [Funtype(bt_i,bt_o)] bt_o st));
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol forall) [Funtype(Funtype(bt_i,bt_o),bt_o)] bt_o st));	
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol equality) [Funtype(bt_i,bt_i);Funtype(bt_i,bt_i)] bt_o st));
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol equality) [Funtype(bt_i,bt_o);Funtype(bt_i,bt_o)] bt_o st));
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (get_defined_symbol st.signature nequals) [bt_i;bt_i] bt_o st));
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (get_defined_symbol st.signature nequals) [Funtype(bt_i,bt_i);Funtype(bt_i,bt_i)] bt_o st));	
			       (xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (get_defined_symbol st.signature nequals) [Funtype(bt_i,bt_o);Funtype(bt_i,bt_o)] bt_o st))
			     ] in
			 match st.flags.prim_subst with
			     0 -> []
			   | 1 -> base_1
			   | 2 -> base_1@base_2
			   | 3 -> base_1@base_2@base_3
			   | 4 -> base_1@base_2@base_3@base_4
			   | _ -> base_1@base_2@base_3@base_4
		     in
		       Util.sysout 0 ("\n Prim_subst applied to clause \n "^(cl_clause_to_string cl));
		       (List.iter (fun (xvar,xterm) -> Util.sysout 3 ("\n "^(to_string xvar)^" <- "^(to_string xterm))) prim_subst_pairs);
			
		       List.flatten
			 (List.map 
			    (fun (var,gb) -> 
			       let newlits = List.map (fun l -> substitute_lit l st  [(var,gb)]) litlist in
			       let new_free_vars = (litlist_free_vars newlits) in
			       let new_clause =
				 mk_clause newlits (inc_clause_count st) new_free_vars 
				   ("prim_subst",[(cl.cl_number, "[bind(" ^ to_string var ^ ", $thf(" ^ to_hotptp gb ^ "))]")], "") cl.cl_origin st
			       in simplify new_clause st
			    )
			    prim_subst_pairs))
		varlist))
  in
     normal_results

(*
  let leibeq_vars_and_argterms = leibniz_eq_heads_and_argterms litlist in
  let special_results =
    match leibeq_vars_and_argterms with
	[] -> []
      | _ ->
	  List.flatten
	    (List.map
	       (fun (var,arg_term) -> 
		  let xvar = term2xterm var in
		  let gb = term2xterm (special_eq_imi_binding arg_term st) in
		  let occurstest = occurs_in st.index gb xvar in
		    (*n Util.sysout 0 ("\n   Testing wheter "^(to_string xvar)^" occurs in "^(to_string gb)^" : "^(string_of_bool occurstest)); *)
		    if occurstest then []
		    else
		      let newlits = List.map (fun l -> substitute_lit l st  [(xvar,gb)]) litlist in
		      let new_free_vars = (litlist_free_vars newlits) in
		      let new_clause = 
			mk_clause newlits (inc_clause_count st) new_free_vars 
			  ("prim_subst",[(cl.cl_number,"[bind("^(to_string xvar)^","^(to_string gb)^")]")],"") cl.cl_origin st
		      in simplify new_clause st
	       )
	       leibeq_vars_and_argterms)
  in
    normal_results@special_results 
*)

   


(** Replacement of Leibniz equalities *)

let replace_leibniz_lits (cl:cl_clause) (st:state) =
  let find_leibniz_varArgCombinations litlist =
    let candidate_heads_pos = 
      List.flatten 
	(List.map 
	   (fun l -> 
	      if l.lit_polarity 
	      then
		match (xterm2term l.lit_term) with
		    Appl(Symbol hd,t) -> 
		      let xvar = term2xterm (Symbol hd) and xargterm = term2xterm t in
			if (not (Term.is_variable (Symbol hd))) || (occurs_in st.index xargterm xvar)
			then []
			else [Symbol hd]
		  | _ -> []
	      else [])
	   litlist)
    in
      List.flatten
	(List.flatten
	   (List.map
	      (fun var ->
		 List.map 
		   (fun l ->
		      if l.lit_polarity then []
		      else
			match (xterm2term l.lit_term) with
			    Appl(Symbol hd,t) -> 
			      if var = (Symbol hd) then 
				let xvar = term2xterm (Symbol hd) and xargterm = term2xterm t in
				  if occurs_in st.index xargterm xvar 
				  then []
				  else [(var,t)]
			      else []
			  | _ -> [])
		   litlist)
	      candidate_heads_pos))
  in
  let litlist = (Array.to_list cl.cl_litarray) 
  in
     match find_leibniz_varArgCombinations litlist with
	(var,argterm)::tl -> 
	  let xvar = term2xterm var in
	    (
	      match special_eq_imi_binding [Term.type_of (type_of_symbol st.signature) argterm] argterm st with
		  [gb] -> 
		    let xgb = term2xterm gb in 
		    let newlits = List.map (fun l -> substitute_lit l st [(xvar,xgb)]) litlist in
		    let new_free_vars = (litlist_free_vars newlits) in
		    let new_clause =
		      mk_clause newlits (inc_clause_count st) new_free_vars 
			("replace_leibnizEQ", [(cl.cl_number, "[bind(" ^ to_string xvar ^ ", $thf(" ^ to_hotptp xgb ^ "))]")], "") cl.cl_origin st
		    in 
		      if (List.length litlist <= 2) then simplify new_clause st else cl::simplify new_clause st
		| _ -> [cl] )
      | _ -> [cl]

	  

(** Replacement of Andrews equalities *)

let replace_andrews_lits (cl:cl_clause) (st:state) =
  Util.sysout 3 ("\n  REPLACE_ANDREWS_EQ: "^(cl_clause_to_protocol cl));  
  let find_andrews_Candidate litlist =
    List.flatten 
      (List.map 
	 (fun l -> 
	    if (not l.lit_polarity) 
	    then
	      (match (xterm2term l.lit_term) with
		   Appl(Appl(Symbol varhd,t1),t2) -> 
		     let arg_ty1 = Term.type_of (type_of_symbol st.signature) t1
		     (* and arg_ty2 = Term.type_of (type_of_symbol st.signature) t2 *)
         in
		       (if ((Term.is_variable (Symbol varhd)) && (t1 = t2)) 
(*
				||
				((Term.is_variable t1) && (arg_ty1 = arg_ty2))
				||
				((Term.is_variable t2) &&  (arg_ty1 = arg_ty2))))
*)
			then
			  let xvar = term2xterm (Symbol varhd)  in
     			  let xbinding = term2xterm (eq_binding arg_ty1 st) in
			    [(xvar,xbinding)]
			else [])
		 | _ -> Util.sysout 5 ("\n  I am here: "^(lit_literal_to_string l)); 
                        [])
            else [])
	 litlist) in
  let litlist = (Array.to_list cl.cl_litarray) in
  let result =
    match find_andrews_Candidate litlist with
	(xvar,xgb)::tl -> 
          let newlits = List.map (fun l -> substitute_lit l st [(xvar,xgb)]) litlist in
	  let new_free_vars = (litlist_free_vars newlits) in
	  let new_clause =
	    mk_clause newlits (inc_clause_count st) new_free_vars 
	      ("replace_andrewsEQ", [(cl.cl_number, "[bind(" ^ to_string xvar ^ ", $thf(" ^ to_hotptp xgb ^ "))]")], "") cl.cl_origin st
	  in 
            Util.sysout 3 ("\n SOMETHINGDONE_REPLACE_ANDREWS_EQ");  
            cl::simplify new_clause st
      | _ -> [cl]
      in
   Util.sysout 3 ("\n  REPLACE_ANDREWS_EQ_RESULT: "^(cl_clauselist_to_protocol result)^"\n");      
   result
	  
(** Replacement of Leibniz or Andrews equalities *)


(*
let replace_defEQ_lits (cl:cl_clause) (st:state) =
  match replace_leibniz_lits cl st with 
      [clnew] -> if clnew = cl then replace_andrews_lits clnew st else [clnew]
    | _ -> replace_andrews_lits cl st 
*)


(** The (Extensional) Pre-Unification Rule *)

let alpha_equal xt1 xt2 st =
 ((get_id st.index xt1) = (get_id st.index xt2)) 

let analyze_unilit (lit:role lit_literal) (st:state) =    
  let is_logical_connective (t:role xterm) =
    match (xterm2im t 1) with
      Xsymbol(s,_) -> 
	(
	 match s with
	   "~" -> true
	 | "|"  -> true
	 | "&" -> true
	 | "~|" -> true
	 | "~&" -> true
	 | "=" -> true
	 | "!=" -> true 
	 | "=>" -> true
	 | "<=" -> true
	 | "<=>" -> true
	 | "<~>" -> true
	 | "!" -> true
	 | "?" -> true
	 | _ -> false
	)
    | _ -> false
  in
  let is_equality (t:role xterm) =
    match (xterm2im t 1) with
	Xsymbol(s,_) -> 
	  (	  
	    match s with
	      | "=" -> true
	      | _ -> false
	  )
      | _ -> false
  in
  let analyze l1 l2 = 
      let xl1 = (im2xterm l1) 
      and xl2 = (im2xterm l2) in
      let xhl1 = get_head xl1 
      and xhl2 = get_head xl2 
      and xargsl1 = get_args xl1
      and xargsl2 = get_args xl2 in
	if 
	  let res = (xl1 = xl2) in
	    ((Util.sysout 3 ( "\n\n TEST1 = "^(to_string xl1)
			     ^"\n TEST2 = "^(to_string xl2)
			     ^"\n RES = "^(string_of_bool res)));
	     res)
	then ("triv",xl1,xl2,[],[]) 
	else
	  match (l1,l2,
		 (is_variable xhl1),(is_variable xhl2),
		 (type_of xl1),(type_of xl2),
		 (is_logical_connective xhl1),(is_logical_connective xhl2),
		 (is_equality xhl1),(is_equality xhl2)) 
	  with
              (Xabstr(_,_,_,_),Xsymbol(_,_),_,true,_,_,_,_,_,_) -> 
	        let occurstest = occurs_in st.index xl1 xl2 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl2)^" occurs in "^(to_string xl1)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("func",xl2,xl1,[],[]) else ("bind",xl2,xl1,[],[])
	    | (Xabstr(_,_,_,_),_,_,_,_,_,_,_,_,_) -> ("func",xl1,xl2,[],[])
            | (Xsymbol(_,_),Xabstr(_,_,_,_),true,_,_,_,_,_,_,_) -> 
                let occurstest = occurs_in st.index xl2 xl1 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl1)^" occurs in "^(to_string xl2)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("func",xl1,xl2,[],[]) else ("bind",xl1,xl2,[],[])
	    | (_,Xabstr(_,_,_,_),_,_,_,_,_,_,_,_) -> ("func",xl1,xl2,[],[])

	    | (Xsymbol(_,_),Xsymbol(_,_),true,true,_,_,_,_,_,_) -> ("flexflex",xl1,xl2,[],[])
	    | (Xsymbol(_,_),Xsymbol(_,_),true,_,_,_,_,_,_,_) -> ("bind",xl1,xl2,[],[])
	    | (Xsymbol(_,_),Xsymbol(_,_),_,true,_,_,_,_,_,_) -> ("bind",xl2,xl1,[],[])
	    | (Xsymbol(_,_),Xsymbol(_,_),false,false,Basetype("$o"),Basetype("$o"),_,_,_,_) -> ("bool",xl1,xl2,[],[]) 
	    | (Xsymbol(_,_),Xsymbol(_,_),false,false,Funtype(_,_),Funtype(_,_),_,_,_,_) -> ("func",xl1,xl2,[],[]) 
	    | (Xsymbol(_,_),Xsymbol(_,_),_,_,_,_,_,_,_,_) -> ("fail",xl1,xl2,[],[]) 

            | (Xsymbol(_,_),Xappl(_,_,_),true,_,Funtype(_,_),Funtype(_,_),_,_,_,_) -> 
	        let occurstest = occurs_in st.index xl2 xl1 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl1)^" occurs in "^(to_string xl2)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("func",xl1,xl2,[],[]) else ("bind",xl1,xl2,[],[])
	    | (Xsymbol(_,_),Xappl(_,_,_),_,_,Funtype(_,_),Funtype(_,_),_,_,_,_) -> ("func",xl1,xl2,[],[]) 
	    | (Xsymbol(_,_),Xappl(_,_,_),false,false,Basetype("$o"),Basetype("$o"),_,_,_,_) -> ("bool",xl1,xl2,[],[])
	    | (Xsymbol(_,_),Xappl(_,_,_),true,_,Basetype("$o"),Basetype("$o"),true,_,_,_) -> 
		let occurstest = occurs_in st.index xl2 xl1 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl1)^" occurs in "^(to_string xl2)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("occurs+bool",xl1,xl2,[],[]) else ("bind+bool",xl1,xl2,[],[])
	    | (Xsymbol(_,_),Xappl(_,_,_),true,_,_,_,_,_,_,_) -> 
		let occurstest = occurs_in st.index xl2 xl1 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl1)^" occurs in "^(to_string xl2)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("occurs",xl1,xl2,[],[]) else ("bind",xl1,xl2,[],[])
	    | (Xsymbol(_,_),Xappl(_,_,_),false,true,_,_,_,_,_,_) -> ("flexrigid",xl2,xl1,[],[])
	    | (Xsymbol(_,_),Xappl(_,_,_),false,false,_,_,_,_,_,_) -> ("fail",xl1,xl2,[],[])

	    | (Xappl(_,_,_),Xsymbol(_,_),_,true,Funtype(_,_),Funtype(_,_),_,_,_,_) -> 
         	let occurstest = occurs_in st.index xl1 xl2 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl2)^" occurs in "^(to_string xl1)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("func",xl2,xl1,[],[]) else ("bind",xl2,xl1,[],[])
	    | (Xappl(_,_,_),Xsymbol(_,_),_,_,Funtype(_,_),Funtype(_,_),_,_,_,_) -> ("func",xl1,xl2,[],[]) 
	    | (Xappl(_,_,_),Xsymbol(_,_),false,false,Basetype("$o"),Basetype("$o"),_,_,_,_) -> ("bool",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xsymbol(_,_),_,true,Basetype("$o"),Basetype("$o"),true,_,_,_) ->  
		let occurstest = occurs_in st.index xl1 xl2 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl2)^" occurs in "^(to_string xl1)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("occurs+bool",xl2,xl1,[],[]) else ("bind+bool",xl2,xl1,[],[])
	    | (Xappl(_,_,_),Xsymbol(_,_),_,true,_,_,_,_,_,_) -> 
		let occurstest = occurs_in st.index xl1 xl2 in
		  Util.sysout 2 ("\n   Testing wheter "^(to_string xl2)^" occurs in "^(to_string xl1)^" : "^(string_of_bool occurstest)); 
		  if occurstest then ("occurs",xl2,xl1,[],[]) else ("bind",xl2,xl1,[],[])
	    | (Xappl(_,_,_),Xsymbol(_,_),true,false,_,_,_,_,_,_) -> ("flexrigid",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xsymbol(_,_),false,false,_,_,_,_,_,_) -> ("fail",xl1,xl2,[],[])

	    | (Xappl(_,_,_),Xappl(_,_,_),true,true,_,_,_,_,_,_) -> ("flexflex",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xappl(_,_,_),false,false,_,_,_,_,true,true) -> 
		if ((List.map type_of xargsl1) = (List.map type_of xargsl2))
		then ("dec=",xl1,xl2,xargsl1,xargsl2)
		else ("fail",xl1,xl2,[],[])
(*
	    | (Xappl(_,_,_),Xappl(_,_,_),false,false,Basetype("$o"),Basetype("$o"),true,_,false,false) -> 
		if  xhl1 = xhl2  then ("dec+bool",xl1,xl2,xargsl1,xargsl2) else ("bool",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xappl(_,_,_),false,false,Basetype("$o"),Basetype("$o"),_,true,false,false) -> 
		if  xhl1 = xhl2  then ("dec+bool",xl1,xl2,xargsl1,xargsl2) else ("bool",xl1,xl2,[],[])
*)
(*
            | (Xappl(_,_,_),Xappl(_,_,_),false,false,Basetype("$o"),Basetype("$o"),_,_,false,false) -> 
		if  xhl1 = xhl2  then ("dec+bool",xl1,xl2,xargsl1,xargsl2) else ("bool",xl1,xl2,[],[])
*)
            | (Xappl(_,_,_),Xappl(_,_,_),false,false,Basetype("$o"),Basetype("$o"),_,_,_,_) -> 
		if  xhl1 = xhl2 && ((List.map type_of xargsl1) = (List.map type_of xargsl2))
                then ("dec+bool",xl1,xl2,xargsl1,xargsl2) 
                else ("bool",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xappl(_,_,_),false,false,_,_,_,_,_,_) -> 
		if  xhl1 = xhl2 && ((List.map type_of xargsl1) = (List.map type_of xargsl2))
                then ("dec",xl1,xl2,xargsl1,xargsl2) 
                else ("fail",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xappl(_,_,_),true,false,Basetype("$o"),Basetype("$o"),_,true,_,_) -> ("flexrigid+bool",xl1,xl2,[],[])
	    | (Xappl(_,_,_),Xappl(_,_,_),false,true,Basetype("$o"),Basetype("$o"),true,_,_,_) -> ("flexrigid+bool",xl2,xl1,[],[])
 	    | (Xappl(_,_,_),Xappl(_,_,_),true,false,_,_,_,_,_,_) -> ("flexrigid",xl1,xl2,[],[])
 	    | (Xappl(_,_,_),Xappl(_,_,_),false,true,_,_,_,_,_,_) -> ("flexrigid",xl2,xl1,[],[])
	    | (_,_,_,_,_,_,_,_,_,_) -> 
		Util.sysout 2 ("\n  FAILURE analyze in pre_unify: left:"^(to_string xl1)^" right: "^(to_string xl2)^"\n");
		raise (Failure "analyze in pre_unify")
  in
  let result = 
    if lit.lit_polarity
    then ("otherlit",lit.lit_term,lit.lit_term,[],[])
    else 
      match (xterm2im lit.lit_term 6) with
	  Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> analyze l1 l2 
	| _ -> ("otherlit",lit.lit_term,lit.lit_term,[],[])
  in    
    
  let (s,t1,t2,lst1,lst2) = result in  
    Util.sysout 3 ("\n\n  Analysis of Lit: "^(lit_literal_to_string lit)^" ---> ("^s^","^(to_string t1)^","^(to_string t2)^","^(List.fold_right (fun t s -> (to_string t)^"|"^s) lst1 "")^","^(List.fold_right (fun t s -> (to_string t)^"|"^s) lst2 "")^")"); 
    
    result

let analyze_flexflex_unilits (lits : role lit_literal list) =
  List.partition (fun l -> is_flexflex_unilit l) lits

let func_ext_terms (t1:term) (t2:term) (st:state) (free_vars:term list) =
  let argty_t1 = arg_type (Term.type_of (type_of_symbol st.signature) t1) in
  let fv_type_list = List.map (fun v -> type_of_symbol st.signature (get_symbol v)) free_vars in
  let sk_const_ty = List.fold_right (fun l1 l2 -> abstr_type l1 l2) fv_type_list argty_t1 in
  let skoconst = create_and_insert_skolem_const (Symbol "E") sk_const_ty st in
  let skoterm =  List.fold_left (fun l1 l2 -> Appl(l1,l2)) skoconst free_vars in
  let (new1,new2) = ((beta_normalize (Appl(t1,skoterm))),(beta_normalize (Appl(t2,skoterm)))) in
  (new1,new2)

let funcOrDecTouched = ref "FuncOrDecTouched"
let getFuncOrDecTouched = !funcOrDecTouched

let func_ext (t1:term) (t2:term) (st:state) (free_vars:term list) =
  let (new1,new2) = func_ext_terms t1 t2 st free_vars in
  lit_mk_uni_literal st.signature (term2xterm new1) (term2xterm new2) getFuncOrDecTouched

let bool_ext st t1 t2 info =  
  [lit_mk_literal st.signature t1 false info; lit_mk_literal st.signature t2 false info],
  [lit_mk_literal st.signature t1 true info; lit_mk_literal st.signature t2 true info]


let make_dec_lits st (termlist1 : role xterm list) (termlist2 : role xterm list) =
  List.map2 (fun t1 t2 -> lit_mk_uni_literal st.signature t1 t2 getFuncOrDecTouched) termlist1 termlist2

let flexrigid_binding_pairs (t1 : term) (t2 : term) (st : state) =
  Util.sysout 3 ("\n :flexrigid_binding_pairs: \n   :t1: " ^
                   Term.to_hotptp t1 ^ "\n   :t2: " ^ Term.to_hotptp t2 ^ "\n");
  let ty1 = Term.type_of (type_of_symbol st.signature) t1
  and ty2 = Term.type_of (type_of_symbol st.signature) t2 in
  let hd1 = Term.get_head_symbol t1
  and hd2 = Term.get_head_symbol t2 in
  let ty_hd1 = Term.type_of (type_of_symbol st.signature) hd1 in

(*"flag" is just a check to make sure that hd{1,2} was found at the head of t{1,2}.
  arg_tys_l{1,2} are the types of the arguments of hd{1,2} in t{1,2}.*)
  let (flag1, arg_tys_l1) = types_of_all_arg_terms_up_to_term t1 hd1 (type_of_symbol st.signature)
  and (flag2, arg_tys_l2) = types_of_all_arg_terms_up_to_term t2 hd2 (type_of_symbol st.signature)
  in
    if Term.is_variable hd1 && (not (Term.is_variable hd2)) &&
      (not (is_basetype ty_hd1)) && flag1 && flag2 then
        let list =
          imi_binding hd1 arg_tys_l1 ty1 hd2 arg_tys_l2 ty2 st ::
            proj_bindings hd1 arg_tys_l1 ty1 st in
        let ordered_list =
          List.sort
            (fun x y ->
               let l1 = List.length (Term.free_vars x)
               and l2 = List.length (Term.free_vars y)
               in
                 if l1 <= l2 then -1 else 1)
            list in
        let result =
          List.map (fun binding -> (term2xterm hd1, term2xterm binding))
            ordered_list
        in
          Util.sysout 3 ("\nt1: "^(Term.to_hotptp t1)^"\nt2: "^(Term.to_hotptp t2)^"\n");
          result
    else raise (Failure "flexrigid_binding_lits in pre_unify")

let substitute_right pairlist subst st =
  List.map (fun (l,r) -> (l,(substitute st.index l subst))) pairlist


let has_choice_hd xterm st =
  let xhd = get_head xterm in
  let hd = (xterm2term xhd) in
      match Term.type_of (type_of_symbol st.signature) hd with
	  Funtype(Funtype(alpha,Basetype("$o")),beta) ->
	    alpha = beta && List.mem hd st.choice_functions 
	| _ -> false

(*Create a result clause from the output of the pre-unification algorithm.*)
let create_res_clause
    (subrule : string)
    (flexflexlits : role lit_literal list)
    (otherlits : role lit_literal list)
    (subst : (role xterm * role xterm) list)
    (st : state)
    (cl : cl_clause) =
  let free_vars = litlist_free_vars (flexflexlits @ otherlits) in
  let new_subst_pre = List.filter (fun (v, t) -> (List.mem (xterm2term v) cl.cl_free_vars)) subst in
  let new_subst = substitute_right new_subst_pre subst st in
  let subst_string_list = List.map (fun (v, t) -> ("bind(" ^ to_hotptp v ^ ",$thf(" ^ to_hotptp t ^ "))")) new_subst in
  let subst_string =
    match subst_string_list with
        [] -> ""
      | hd :: tl ->
          "[" ^ List.fold_left (fun s sub -> s ^ "," ^ sub) hd tl ^ "]"
  in
  let cl_new =
    mk_clause (otherlits @ flexflexlits) (inc_clause_count st) free_vars
      ("extuni" ^ subrule, [(cl.cl_number, subst_string)], "") cl.cl_origin st
  in
	let _ = Util.sysout 3 ("\n\ new_clause: " ^ cl_clause_to_protocol cl)
  in               
    cl_new

let create_intermediate_uni_step
    (subrule : string)
    (flexflexlits : role lit_literal list)
    (otherlits : role lit_literal list)
    (subst : (role xterm * role xterm) list)
    (st : state)
    (from_cl : cl_clause) =
  if st.flags.expand_extuni then
    create_res_clause subrule flexflexlits otherlits subst st from_cl
  else from_cl

let sub (pair:((role xterm) * (role xterm))) (st:state) (lits:(role lit_literal) list) = 
  List.map 
    (fun l -> substitute_lit ~info:getFuncOrDecTouched l st [pair])
    lits


let arg_types_are_compatible list1 list2 st =    
   List.length list1 = List.length list2
 &&
   List.for_all (fun x -> x) 
     (List.map2 (fun arg1 arg2 -> (type_of arg1) = (type_of arg2))
         list1 list2)
    


let rec choicehelp l r uniliterals st =
  Util.sysout 3 ("\n choicehelp: "^(Term.to_string l)^"  "^(Term.to_string r));
  match (l,r) with
      (Appl(Symbol choice,p),q) -> 
        Util.sysout 3 ("\n choicehelp: A"); 
	let qtype = Term.type_of (type_of_symbol st.signature) q in
	  (match qtype with
	      Basetype("$o") 
               (*
		let newlit1 = lit_mk_neg_literal (term2xterm q) in
		let newlit2 = lit_mk_pos_literal (term2xterm q) in
		  (newlit1::uniliterals,newlit2::uniliterals)
               *)
	    | _ ->
		let var = create_and_insert_new_free_var_with_simple_name qtype st in
		let newlit1 = (lit_mk_neg_literal st.signature (term2xterm (beta_normalize (Appl(p,var))))) in
		let newlit2 = (lit_mk_pos_literal st.signature (term2xterm (beta_normalize (Appl(p,(Appl(Symbol choice,p))))))) in
		let newlit3 = (lit_mk_pos_literal st.signature (term2xterm (beta_normalize (Appl(p,var))))) in
		let newlit4 = (lit_mk_neg_literal st.signature (term2xterm (beta_normalize (Appl(p,(Appl(Symbol choice,(Abstr(var,qtype,(Appl(Symbol("~"),(Appl(p,var))))))))))))) in
		  ([newlit1;newlit2]@uniliterals,[newlit3;newlit4]@uniliterals,true)
	  )
    | (Appl(l1,l2),Appl(r1,r2)) -> 
           Util.sysout 3 ("\n choicehelp: B"); 
           if arg_types_are_compatible [term2xterm l2] [term2xterm r2] st 
           then 
             let newunilit = lit_mk_uni_literal st.signature (term2xterm l2) (term2xterm r2) "" in
               choicehelp l1 r1 (newunilit::uniliterals) st
           else ([],[],false)
    | _ -> ([],[],false)

(*This code is not actually used in Leo2 -- see "pre_unify_new" instead.*)
(*Wrapper for Leo2's extensional pre-unification algorithm. It defines the algorithm
  internally, and only uses the algorithm if there is a unification literal in "cl";
  otherwise it returns "cl".*)
let pre_unify_ext (cl : cl_clause) (st : state) =
  (*This is Leo2's extensional pre-unification algorithm.
    It consumes "tuples" (explained below) *)
  let rec pre_unify'
      (* "tuples" contains unilits, flexflexlits, otherlits, subst:
         these stand for unification literals, flex-flex literals, other literals
         and substitutions.

         All literals start out in unilits, then are classified by "analyze_unilit"
         into flexflex, other lits (i.e., not unification literals), and classifies
         non-flexflex unification literals (as trivial, flexflex, bind, etc).
         Unification literals may become otherlits (e.g. see mention of "a = b").
         All (not just the head) literals may be instantiated during the course of
         unification. This applies to literals in the current "unification problem",
         not in other (i.e., "other_tuples").

         Each tuple may potentially:
           * give rise to a clause, or
           * result in a transformed tuple, or
           * produce other new tuples (e.g. in the case of flexrigid).
      *)
      (tuples : (role lit_literal list *
                   role lit_literal list *
                   role lit_literal list *
                   (role xterm * role xterm) list) list)
      (st : state)
      (* Accumulates clauses which are to be added to the search space
         These are added as a single clause at the end of the search, as an "extuni" inference.*)
      (accu : cl_clause list)
      (*FIXME this parameter does not appear to be used, since
              it's currently not checked anywhere.*)  
      (depth : int)
      (*FIXME not fully sure how this works*)  
      (something_done : bool) =
    begin
      (*Produce a trace for debugging*)
      let tuplestring =
        List.fold_right
          (fun (ul, ffl, ol, subst) s ->
             let subst_string = List.fold_right (fun (v, t) s -> (" " ^ to_string v ^ "/" ^ to_string t ^ " " ^ s)) subst "" in
               ("\n ul=[" ^ lit_litlist_to_protocol ul ^ "]\n ffl=[" ^ lit_litlist_to_protocol ffl ^ "]\n ol=[" ^ lit_litlist_to_protocol ol ^ "]\n subst=[" ^ subst_string ^ "]\n" ^ s)) tuples ""
      in
        Util.sysout 3 ("\n\nEnter pre_unify' with: " ^ tuplestring ^ "st-not-printed,accu-not-printed," ^ string_of_int depth ^ "," ^ string_of_bool something_done);

        (*The algorithm*)
        (* if depth > st.flags.max_uni_depth then accu else  *)
        match tuples with
            [] -> (* no more to do; give back the clauses in the accumulator *)
              (Util.sysout 3 "\n I am here";
               accu)
          | (unilits, flexflexlits, otherlits, subst) :: rest_tuples -> (* we work on the first tuple *)
              if List.length subst > st.flags.max_uni_depth (* || (depth > st.flags.max_uni_depth) *)
              then pre_unify' rest_tuples st accu depth something_done
              else
                begin
                  match unilits with
                      [] -> (* new solution found -- provided that the flexflexlits are indeed all flexflex,
                               since they might have been instantiated by "bind"s during the course of unification.*)
                        if List.exists (fun lit -> not (is_flexflex_unilit lit)) flexflexlits then
                          (* recurse on the non flexflex literals *)
                          let (ff, noff) = analyze_flexflex_unilits flexflexlits
                          in pre_unify' ((noff, ff, otherlits, subst) :: rest_tuples) st accu depth something_done
                        else
                          (* new solution found; recurse on rest_tuples and add a new clause to accumulator *)
                          if something_done then
                            let new_cl_list = simplify (create_res_clause "" flexflexlits otherlits subst st cl) st
                            in pre_unify' rest_tuples st (new_cl_list @ accu) depth true(*FIXME shouldn't this be reset to "false"?*)  
                          else
                            pre_unify' rest_tuples st accu depth false
                    | lit :: rest_unilits -> (* work on first unification literal *)
                        begin
                          match analyze_unilit lit st with
                              ("otherlit",_,_,_,_) -> (* the lit is not a unification literal;
                                                         move to otherlits and recurse
                                                         example: (p a)^T
                                                      *)
                                pre_unify' ((rest_unilits, flexflexlits, lit :: otherlits, subst) :: rest_tuples) st accu depth something_done
                            | ("fail",_,_,_,_) -> (* failure check was positive; recurse on rest_tuples
                                                     example: a = b
                                                     only in special situations (two unilits) allow for test of second lit to allow
                                                     the return of one negated equation
                                                  *)
                                (*FIXME The logic of this block of code isn't clear*)  
                                if
                                  (List.length rest_unilits = 1 && List.length otherlits = 0) ||
                                    (something_done && List.length rest_unilits = 0 && List.length otherlits = 0)
                                then
                                  pre_unify' ((rest_unilits, flexflexlits, lit :: otherlits, subst) :: rest_tuples) st accu depth something_done
                                else
                                  pre_unify' rest_tuples st accu depth true
                            | ("occurs",_,_,_,_) -> (* occurs check was positive; recurse on rest_tuples
                                                       example: X =^{i} (f X)
                                                    *)
                                pre_unify' rest_tuples st accu depth true
                            | ("occurs+bool",t1,t2,_,_) -> (* occurs check was positive but terms are of Boolean type;
                                                              apply Boolean extensionality and recurse;
                                                              example: X =^{o} (or X Y)
                                                           *)
                                let (newlits1, newlits2) = bool_ext st t1 t2 lit.lit_info
                                in
                                  (*FIXME why are newlits{1,2} put in otherlits, rather than unilits?*)  
                                  pre_unify' ((rest_unilits, flexflexlits, newlits1 @ otherlits, subst) ::
                                                ((rest_unilits, flexflexlits, newlits2 @ otherlits, subst) :: rest_tuples)) st accu depth true
                            | ("bind",v,t,_,_) -> (* solved unification literal; apply binding and recurse
                                                     example: X = t
                                                  *)
                                let new_tuple = (sub (v, t) st rest_unilits,
                                                 sub (v, t) st flexflexlits,
                                                 sub (v,t) st otherlits,
                                                 subst @ [(v, t)])
                                in pre_unify' (new_tuple :: rest_tuples) st accu depth true
                            | ("bind+bool",v,t,_,_) -> (* solved unification literal and terms are of Boolean type;
                                                          apply binding and recurse, but also apply boolean extensionality
                                                          example: X =^{o} (or t1 t2)
                                                       *)
                                let new_tuple = (sub (v, t) st rest_unilits,
                                                 sub (v, t) st flexflexlits,
                                                 sub (v, t) st otherlits,
                                                 subst @ [(v, t)]) in
                                let (newlits1, newlits2) = bool_ext st v t lit.lit_info
                                in
                                  pre_unify' ((rest_unilits, flexflexlits, newlits1 @ otherlits, subst) ::
                                                ((rest_unilits, flexflexlits, newlits2 @ otherlits, subst) ::
                                                   new_tuple :: rest_tuples)) st accu depth true
                            | ("triv",_,_,_,_) -> (* trivial unification literal; recurse;
                                                     example: a = a
                                                  *)
                                pre_unify' ((rest_unilits, flexflexlits, otherlits, subst) :: rest_tuples) st accu depth true
                            | ("flexflex",t1,t2,_,_) -> (* flexflex unification literal; move it and recurse
                                                           example: (H a) = (G b)
                                                        *)
                                pre_unify' ((rest_unilits, lit :: flexflexlits, otherlits, subst) :: rest_tuples) st accu depth true
                            | ("func",t1,t2,_,_) -> (* functional unification literal; apply extensionality and recurse
                                                       example: (f a) =^{a->b} (g b c)
                                                    *)
                                let free_vars = litlist_free_vars (unilits @ flexflexlits @ otherlits) in
                                let newlit = func_ext (xterm2term t1) (xterm2term t2) st free_vars
                                in
                                  pre_unify' ((newlit :: rest_unilits, flexflexlits, otherlits, subst) :: rest_tuples) st accu depth true
                            | ("bind+func",t1,t2,_,_) -> (* functional unification literal; apply extensionality and recurse
                                                            example: (f a) =^{a->b} (g b c)
                                                         *)
                                let new_tuple = (sub (t1, t2) st rest_unilits,
                                                 sub (t1, t2) st flexflexlits,
                                                 sub (t1,t2) st otherlits,
	                                               subst @ [(t1, t2)]) in
                                let free_vars = litlist_free_vars (unilits @ flexflexlits @ otherlits) in
                                let newlit = func_ext (xterm2term t1) (xterm2term t2) st free_vars
                                in
                                  pre_unify' ((newlit :: rest_unilits, flexflexlits, otherlits, subst) ::
                                                new_tuple :: rest_tuples) st accu depth true
                            | ("dec",hd1,hd2,args1,args2) -> (* decomposition unification literal; decompose and recurse
                                                                example:  (f a b) = (f c d)
                                                             *)
                                let newlits = make_dec_lits st args1 args2
                                in
                                  pre_unify' ((newlits @ rest_unilits, flexflexlits, otherlits, subst) ::
                                                (rest_unilits, flexflexlits, newlits @ otherlits, subst) ::
                                                rest_tuples) st accu depth true
                            | ("dec=",hd1,hd2,args1,args2) -> (* decomposition unification literal; decompose and recurse
                                                                 example:  (= a b) = (= c d)
                                                              *)
                                let newlits1 = make_dec_lits st args1 args2 and
                                    newlits2 = make_dec_lits st (List.rev args1) args2
                                in
                                  pre_unify' ((newlits1 @ rest_unilits, flexflexlits, otherlits, subst) ::
                                                (newlits2 @ rest_unilits, flexflexlits, otherlits, subst) ::
                                                (* new for BrownSmolk-3.thf *)
                                                (rest_unilits, flexflexlits, newlits1 @ otherlits, subst) ::
                                                (* new for BrownSmolk-3.thf *)
                                                (rest_unilits, flexflexlits, newlits2 @ otherlits, subst) ::
                                                rest_tuples) st accu depth true
                            | ("dec+bool",t1,t2,args1,args2) -> (* decomposition unification literal; decompose,
                                                                   apply Boolean extensionality and recurse
                                                                   example:  (f a b) = (f c d)
                                                                *)
                                let newlits = make_dec_lits st args1 args2 in
                                let (newlits1,newlits2) = bool_ext st t1 t2 lit.lit_info
                                in
                                  pre_unify'  ((rest_unilits, flexflexlits, newlits1 @ otherlits, subst) ::
                                                 (rest_unilits, flexflexlits, newlits2 @ otherlits, subst) ::
                                                 (newlits @ rest_unilits, flexflexlits, otherlits, subst) ::
                                                 (* new for BrownSmolk-3.thf *)
                                                 (rest_unilits, flexflexlits, newlits @ otherlits, subst) ::
                                                 rest_tuples) st accu depth true
                            | ("bool",t1,t2,[],[]) -> (* Boolean unification literal;
                                                         apply Boolean extensionality and recurse
                                                         example:  (or a b) = (f c d)
                                                      *)
                                let (newlits1,newlits2) = bool_ext st t1 t2 lit.lit_info
                                in
                                  pre_unify'  ((rest_unilits, flexflexlits, newlits1 @ otherlits, subst) ::
                                                 (rest_unilits, flexflexlits, newlits2 @ otherlits, subst) ::
                                                 rest_tuples) st accu depth true
                            | ("flexrigid",t1,t2,_,_) -> (* flexrigid unification literal;
                                                            determine bindings and recurse with increased depth
                                                            example: (H a) = (g b)
                                                         *)
                                let bindingpairs = flexrigid_binding_pairs (xterm2term t1) (xterm2term t2) st in
                                  Util.sysout 3 ("\n Bindingpairs: " ^
                                                   List.fold_right (fun (v, t) s ->
                                                                      ("(" ^ to_string v ^ "," ^ to_string t ^ ")," ^ s))
                                                   bindingpairs "");
                                  let new_tuples =
                                    List.map (fun (v, t) ->
                                                (sub (v, t) st unilits,
                                                 sub (v, t) st flexflexlits,
                                                 sub (v, t) st otherlits,
                                                 subst @ [(v, t)]))
                                      bindingpairs in
                                  let tuplestring =
                                    List.fold_right (fun (ul, ffl, ol, subst) s ->
                                      "(" ^ lit_litlist_to_protocol ul ^ "," ^ lit_litlist_to_protocol ffl ^
                                        "," ^ lit_litlist_to_protocol ol ^ ",subst-not-printed)," ^ s) new_tuples ""
                                  in
                                    Util.sysout 3 ("\n  new_tuples: " ^ tuplestring);
                                    pre_unify' (new_tuples @ rest_tuples) st accu (depth + 1) true
                            | ("flexrigid+bool",t1,t2,_,_) -> (* flexrigid unification literal and terms are of Boolean type;
                                                                 determine bindings and recurse with increased depth,
                                                                 but also apply Boolean extensionality
                                                                 example: (H a) =^{o} (or t1 t2)
                                                              *)
                                let bindingpairs = flexrigid_binding_pairs (xterm2term t1) (xterm2term t2) st in
                                  Util.sysout 3 ("\n Bindingpairs: " ^
                                                   List.fold_right (fun (v, t) s ->
                                                                      "(" ^ to_string v ^ "," ^ to_string t ^ ")," ^ s)
                                                   bindingpairs "");
                                  let new_tuples =
                                    List.map (fun (v, t) ->
                                                (sub (v, t) st unilits,
                                                 sub (v, t) st flexflexlits,
                                                 sub (v, t) st otherlits,
                                                 subst @ [(v, t)]))
                                      bindingpairs in
                                  let (newlits1, newlits2) = bool_ext st t1 t2 lit.lit_info
                                  in
                                    pre_unify' ((rest_unilits, flexflexlits, newlits1 @ otherlits, subst) ::
                                                  (rest_unilits, flexflexlits, newlits2 @ otherlits, subst) ::
                                                  new_tuples @ rest_tuples) st accu (depth + 1) true
                            | _ -> raise (Failure "Unknown case returned by analyze_unilit")
                        end
                end
    end in
  let litlist = Array.to_list cl.cl_litarray
  in
    if List.exists (fun l -> is_unilit l) litlist then
      pre_unify' [(litlist, [], [], [])] st [] 1 false
    else [cl]

(*
let clash (l:role lit_literal) =
  if l.lit_polarity then false 
  else
    match (xterm2im l.lit_term 3) with
	Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	  let t1 = (get_head_symbol  (im2xterm l1)) and t2 = (get_head_symbol (im2xterm l2)) in
	    Util.sysout 0 ("\n  :term1: "^(to_string t1)^"  :term2: "^(to_string t2));
	    (not (is_variable t1)) && (not (is_variable t2)) && (not (t1 = t2))
      | _ -> false
*)
	  
	  
let uni_termpairs (l:role lit_literal) =
  match (xterm2im l.lit_term 4) with
      Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> (l1,l2)
    | _ -> raise (Failure "uni_termpairs")

let switch st (l:role lit_literal) =
  match (xterm2im l.lit_term 4) with
      Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) -> lit_mk_uni_literal st.signature (im2xterm l2) (im2xterm l1) l.lit_info
    | _ -> raise (Failure "switch_uni_termpairs")

(*Leo2's extensional pre-unification algorithm.
  It usually starts with the call:
	  pre_uni_new' litlist [] [] [] st 0 0 st.flags.use_extuni
  where "litlist" is the list of literals in a clause. These are then
  classified by pre_uni_new' into unilits, flexflexlits, and otherlits.
  It produces a list of 5-tuples consisting of flex-flex literals,
  other literals, substitutions, the number of extuni inferences carried out,
  and the previous inferred clause.
  (Substitutions are used to create the "bind" annotations in the proof protocol.)
  Each resulting tuple becomes a clause.
  Intuitively, pre_uni_new' could return
    * an empty list, in which case unification could not drive the proof further.
    * a singleton list, which is equisatisfiable with the original clause
    * multiple tuples, each of which is equisatisfiable with the original clause.
  For instance, apply flexrigid can produce a list of tuples,
  while triv returns a smaller unilist.
  All literals are subject to transformation by the substitutions.
*)
let rec pre_uni_new'
    (*All literals are initially placed here.
      Unification literals are processed. Flexflex
      literals are transferred to flexlits, and
      non-unification literals are transferred to
      otherlits.*)
    (unilits : role lit_literal list)
    (*Flex-Flex literals*)
    (flexlits : role lit_literal list)
    (*Non-unification literals*)
    (otherlits : role lit_literal list)
    (*Accummulated substitutions*)
    (subst : (role xterm * role xterm) list)
    (*State*)
    (st : state)
    (*"unification depth", which actually measures
      the number of applications of flex_rigid.*)
    (depth : int)
    (*Whether algorithm should operate extensionally*)
    (flag_ext : bool)
    (*Number of changes so far*)
    (changes : int)
    (*Previous clause in the derivation.*)
    (cl : cl_clause) =
  State.check_timeout ();
  let subststring = List.fold_right (fun (v, t) s -> (" " ^ to_string v ^ "/" ^ to_string t ^ " " ^ s)) subst "" in
    Util.sysout 3 ("\n pre_uni_new': \n  :unilits: " ^ lit_litlist_to_protocol unilits ^ "\n  :flexlits: " ^
                     lit_litlist_to_protocol flexlits ^ "\n  :otherlits: " ^ lit_litlist_to_protocol otherlits ^
                     "\n  :subst: " ^ subststring ^ "\n  :depth: " ^ string_of_int depth ^
                     "  :flag_ext: " ^ string_of_bool flag_ext);

    if depth >= st.flags.max_uni_depth then []
    else
      match unilits with
        [] ->
          begin
            match analyze_flexflex_unilits flexlits with
                (_, []) ->
                  (* all flex_flex, we are done *)
                  [(flexlits, otherlits, subst, changes, cl)]
              | (ff, notff) ->
                  (* start over with nonflex *)
                  pre_uni_new' notff ff otherlits subst st depth flag_ext changes cl
          end
        | lit :: restlits when is_flexflex_unilit lit ->
            (* move to flexflex *)
            pre_uni_new' restlits (lit :: flexlits) otherlits subst st depth flag_ext changes cl
        | lit :: restlits when not (is_unilit lit) ->
            (* move to otherlits *)
            pre_uni_new' restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl
        | lit :: restlits ->
            (*lit must therefore be a non-flexflex unification literal*)
            let (l, r) = uni_termpairs lit in
            let (xl, xr) = (im2xterm l, im2xterm r) in
            let decFuncProcessed = (lit.lit_info = getFuncOrDecTouched) 
            in
              match (l, r, flag_ext) with
                  (*Note that flex-flex literals have already been handled.
                    Since "l" is a variable, then this must be a "bind" step*)
                  (Xsymbol (s, ty), _, _) when is_variable xl ->
                    if occurs_in st.index xr xl then []
                    else
                      (* bind *)
                      let unilits' = sub (xl, xr) st restlits in
                      let flexlits' = sub (xl, xr) st flexlits in
                      let otherlits' = sub (xl, xr) st otherlits in
                      let subst' = (xl, xr) :: subst in
                        (*should unilits' be given in separate argument below?*)  
                      let cl' = create_intermediate_uni_step "_bind" flexlits' (otherlits' @ unilits') subst' st cl
                      in
                        pre_uni_new' unilits' flexlits' otherlits' subst' st depth flag_ext (changes + 1) cl'
                | (_, Xsymbol (s, ty), _) when is_variable xr ->
                    (*Reorienting equalities isn't tracked*)
                    pre_uni_new' (switch st lit :: restlits) flexlits otherlits subst st depth flag_ext changes cl
                | (Xsymbol _, Xsymbol _, false) ->
                    (*Note that neithr "l" nor "r" is a variable, since they would have been picked up
                      by the previous two rules.
                      Therefore here we're dealing with either triv or func steps.*)
                    if xl = xr then
                      let cl' = create_intermediate_uni_step "_triv" flexlits (otherlits @ restlits) subst st cl
                      in
                        pre_uni_new' restlits flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                    else [] 
                | (Xsymbol _, Xsymbol _, true) ->
                    (* Both l and r are constants, since otherwise would have been picked up at the
                       flexflex stage.
                       apply bool at type $o, give back the lits if at other base type, otherwise func *)
                    if xl = xr then
                      let cl' = create_intermediate_uni_step "_triv" flexlits (otherlits @ restlits) subst st cl
                      in
                        pre_uni_new' restlits flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                    else
                      begin
                        let xl_ty = type_of xl in
                        let xr_ty = type_of xr in
                          IFDEF DEBUG THEN
                            assert (xl_ty = xr_ty);
                          END;
                          match (xl_ty, xr_ty, decFuncProcessed) with
                              (Funtype _, Funtype _, _) ->
                                let free_vars = litlist_free_vars (unilits @ flexlits @ otherlits) in
                                let newlit = func_ext (xterm2term xl) (xterm2term xr) st free_vars in
                                let cl' = create_intermediate_uni_step "_func" flexlits (otherlits @ newlit :: restlits) subst st cl
                                in
                                  pre_uni_new' (newlit :: restlits) flexlits otherlits subst st depth flag_ext (changes + 1) cl'
(*FIXME in line below, why "i > 0"? what's special about "i = 0"?
        i=0 means that "dec" has not been applied yet. but this is rather
        arbitrary, since reordering the literals in the clause can give
        different result.
        e.g. in [(f a =?= g b); (c =?= d)], i=1 when we come to process "c =?= d",
        but in [(c =?= d); (f a =?= g b)] i=0 when we come to process "c =?= d".*)  
                            | (Basetype "$o", Basetype "$o",true) ->
                                let (newlits1, newlits2) = bool_ext st xl xr lit.lit_info in
                                let cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                                let cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl
                                in
                                  pre_uni_new' restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) cl1 @
                                    pre_uni_new' restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) cl2
                            | (Basetype _, Basetype _,true) ->
                                (*e.g., (a : $i) = b*)
                                pre_uni_new' restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl
                            | _ -> [] (* fail *)
                                (* assert false (*type must have been different -- this is not possible*) *)
                      end
                | (Xabstr _, _, _)
                | (_, Xabstr _, _) ->
                    (* func *)
                    if xl = xr then
                      let cl' = create_intermediate_uni_step "_triv" flexlits (otherlits @ restlits) subst st cl
                      in
                        pre_uni_new' restlits flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                    else
                      let free_vars = litlist_free_vars (unilits @ flexlits @ otherlits) in
                      let newlit = func_ext (xterm2term xl) (xterm2term xr) st free_vars in
                      let cl' = create_intermediate_uni_step "_func" flexlits (otherlits @ newlit :: restlits) subst st cl
                      in
                        pre_uni_new' (newlit :: restlits) flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                | (Xsymbol _, Xappl _, _) ->
                    pre_uni_new' (switch st lit :: restlits) flexlits otherlits subst st depth flag_ext changes cl
                | (Xappl _, Xsymbol _, false)
                | (Xappl _, Xappl _, false) ->
                    if xl = xr then
                      let cl' = create_intermediate_uni_step "_triv" flexlits (otherlits @ restlits) subst st cl
                      in
                        pre_uni_new' restlits flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                    else
                      begin
                        let hl = get_head_symbol xl
                        and hr = get_head_symbol xr
                        in
                          match (hl = hr, is_variable hl, is_variable hr) with
                              (_, true, true) ->
                                (* flex_flex *)
                                assert false (*this should never be called, since flexflex literals should have already been handled*)
                            | (true, false, false) ->
                                (* dec *)
                                (*Check for cases like the following:
                                  (a =_i b) =_o (f =_(i>i) g)
                                  since "=" is polymorphic in Leo2.
                                  i.e, just checking "hl = hr" could be misleading unless we also check their types.
                                *)
                                if (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) then
                                  (*Since flag_ext=false we treat "=" as an uninterpreted constant, and decompose.*)
                                  let newlits = make_dec_lits st (get_args xl) (get_args xr) in
                                  let cl' = create_intermediate_uni_step "_dec" flexlits (otherlits @ newlits @ restlits) subst st cl
                                  in
                                    pre_uni_new' (newlits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                                else (* fail *) [] 
                            | (false, false, true) ->
                                (* rigid_flex *)
                                pre_uni_new' (switch st lit :: restlits) flexlits otherlits subst st depth flag_ext changes cl
                            | (false, true, false) ->
                                (* flex_rigid *)
                                List.flatten
                                  (List.map
                                     (fun s ->
                                        let unilits' = sub s st unilits (*This must be unilits, not restlits*) in
                                        let flexlits' = sub s st flexlits in
                                        let otherlits' = sub s st otherlits in
                                        let subst' = s :: subst in
                                        let cl' = create_intermediate_uni_step "_flex_rigid" flexlits' (otherlits' @ unilits') subst' st cl
                                        in
                                          pre_uni_new' unilits' flexlits' otherlits' subst' st (depth + 1) flag_ext (changes + 1) cl')
                                     (*Here could also look at instantiating with logical constants
                                       if the flex literal has boolean value.
                                       I think something similar is done in the primsubst code.*)
                                     (flexrigid_binding_pairs (xterm2term xl) (xterm2term xr) st))
                            | (false, false, false) -> [] 
(*
In literal structure would be useful to have a flag to cache the literal's "status", to
avoid redoing the computation related to classifying a literal.
*)
                            | (true, false, true)
                            | (true, true, false) ->
                                (*these cases don't make sense, so complain*)
                                assert false
                      end
                | (Xappl _, Xsymbol _, true)
                | (Xappl _, Xappl _, true) ->
                    if xl = xr then
                      let cl' = create_intermediate_uni_step "_triv" flexlits (otherlits @ restlits) subst st cl
                      in
                        pre_uni_new' restlits flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                    else
                      begin
                        let hl = get_head_symbol xl
                        and hr = get_head_symbol xr
                        in
                          match (hl = hr, is_variable hl, is_variable hr, type_of xl, type_of xr, decFuncProcessed) with
                              (_, true, true, _, _, _) ->
                                (* flex_flex *)
                                assert false (*this should never be called, since flexflex literals should have already been handled*)
                            | (true, false, false, Basetype "$o", Basetype "$o",true) ->
                                (* dec + apply bool at type $o *)
                                begin
                                  match (xterm2im hl 3, xterm2im hr 3) with
                                    | (Xsymbol ("|", _), Xsymbol ("|", _))
                                    | (Xsymbol ("=", _), Xsymbol ("=", _)) ->
                                        (* symmetry dec + apply bool at type $o *)
                                        let (newlits1, newlits2) = bool_ext st xl xr getFuncOrDecTouched in
                                        let bool_cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                                        let bool_cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl in
                                          if (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) then
                                            (*this is always the case when hl=hr="|"*)
                                            let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                                            let dec_lits_commuted = make_dec_lits st (List.rev (get_args xl)) (get_args xr) in
                                            let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                                            let dec_cl2 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits_commuted @ restlits) subst st cl
                                            in
                                              pre_uni_new' restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                                                pre_uni_new' restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2 @
                                                pre_uni_new' (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 @
                                                pre_uni_new' (dec_lits_commuted @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl2
                                          else
                                              pre_uni_new' restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                                                pre_uni_new' restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2
                                    | _ ->
                                        (* normal dec + apply bool at type $o *)
                                        let (newlits1, newlits2) = bool_ext st xl xr lit.lit_info in
                                        let bool_cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                                        let bool_cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl in
                                        let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                                        let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                                          pre_uni_new' restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                                            pre_uni_new' restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2 @
                                            pre_uni_new' (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1
                                end
                            | (true, false, false, Basetype _, Basetype _,true) -> 
                                (* dec + give back the lits if at other base type *)
                                begin
                                  match (xterm2im hl 3, xterm2im hr 3) with
                                    | (Xsymbol ("=", _), Xsymbol ("=", _)) ->
                                        (* symmetry dec + apply bool at type $o *)
                                        if (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) then
                                          let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                                          let dec_lits_commuted = make_dec_lits st (List.rev (get_args xl)) (get_args xr) in
                                          let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                                          let dec_cl2 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits_commuted @ restlits) subst st cl
                                          in
                                            pre_uni_new' (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 @
                                              pre_uni_new' restlits flexlits (dec_lits_commuted @ otherlits) subst st depth flag_ext (changes + 1) dec_cl2 @
                                              pre_uni_new' (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 @
                                              pre_uni_new' restlits flexlits (dec_lits_commuted @ otherlits) subst st depth flag_ext (changes + 1) dec_cl2
                                        else []
                                   | _ ->
                                        let l_arg_types = List.map type_of (get_args xl)
                                        in
                                          if l_arg_types = (List.map type_of (get_args xr)) then
                                            if List.length l_arg_types = 0 then
                                              pre_uni_new' restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl
                                            else
                                              let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                                              let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl
                                              in
                                                pre_uni_new' restlits flexlits (lit :: otherlits) subst st depth flag_ext (changes + 1) cl @
                                                  pre_uni_new' (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1
                                                  (*
                                                  (*FIXME interesting example: move unilit to otherlits, and leave decfuncdepth unchanged there*)  
                                                    pre_uni_new' restlits flexlits (lit :: otherlits) subst st depth decfuncdepth flag_ext @
                                                    pre_uni_new' (make_dec_lits (get_args xl) (get_args xr) @ restlits) flexlits otherlits subst st depth (decfuncdepth + 1) flag_ext
                                                  *)
                                                  (* else (\* fail *\) [] *)
                                          else
                                            (*This case is nonsensical, since would have cases like
                                              g X Y =?= g Z
                                              or
                                              g X =?= g Z
                                              where X and Z are typed differently.
                                              This suggests a type error somewhere.
                                              Note that such cases might arise with quantifiers,
                                              e.g. (! x : 'a. P a) =?= (! x : 'b. Q b), but these
                                              are handled separately above since the overall type is $o.
                                            *)
                                            assert false
                                end
                            | (true, false, false, _, _, _) ->
                                (* dec *)
                                if (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) then
                                  let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                                  let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl
                                  in
                                    pre_uni_new' (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1
                                else (* fail *) []
                            | (false, false, true, _, _, _) ->
                                (* switch *)
                                pre_uni_new' (switch st lit :: restlits) flexlits otherlits subst st depth flag_ext changes cl
                            | (false, true, false, _, _, _) ->
                                (* flex_rigid *)
                                List.flatten
                                  (List.map
                                     (fun s ->
                                        let unilits' = sub s st unilits (*This must be unilits, not restlits*) in
                                        let flexlits' = sub s st flexlits in
                                        let otherlits' = sub s st otherlits in
                                        let subst' = s :: subst in
                                        let cl' = create_intermediate_uni_step "_flex_rigid" flexlits' (otherlits' @ unilits') subst' st cl
                                        in
                                          pre_uni_new' unilits' flexlits' otherlits' subst' st (depth + 1) flag_ext (changes + 1) cl')
                                     (flexrigid_binding_pairs (xterm2term xl) (xterm2term xr) st))
                            | (false, false, false, Funtype _, Funtype _, _) ->
                                (*"false, false, false" means we have a problem of form
                                  cA H1 ... Hn =?= cB J1 ... Jm
                                *)
                                (* func *)
                                let free_vars = litlist_free_vars (unilits @ flexlits @ otherlits) in
                                let newlit = func_ext (xterm2term xl) (xterm2term xr) st free_vars in
                                let cl' = create_intermediate_uni_step "_func" flexlits (otherlits @ newlit :: restlits) subst st cl
                                in
                                  pre_uni_new' (newlit :: restlits) flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                            | (false, false, false, Basetype "$o", Basetype "$o",true)   ->
                                (* bool *)
                                let (newlits1, newlits2) = bool_ext st xl xr lit.lit_info in
                                let bool_cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                                let bool_cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl
                                in
                                  pre_uni_new' restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                                    pre_uni_new' restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2 @
                                    pre_uni_new' (newlits1 @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) bool_cl1 @
                                    pre_uni_new' (newlits2 @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) bool_cl2
                            | (false, false, false, Basetype _, Basetype _,true) ->
                                pre_uni_new' restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl
(*FIXME raise exception if types differ? *)  

                            | _ ->  (* fail *) [] 
                            (* | _ ->  assert false (*which cases are remaining?*)   *)
                      end
                | _ ->  raise (Failure "pre_uni_new'")



let rec pre_uni_new2
    (*All literals are initially placed here.
      Unification literals are processed. Flexflex
      literals are transferred to flexlits, and
      non-unification literals are transferred to
      otherlits.*)
    (unilits : role lit_literal list)
    (*Flex-Flex literals*)
    (flexlits : role lit_literal list)
    (*Non-unification literals*)
    (otherlits : role lit_literal list)
    (*Accummulated substitutions*)
    (subst : (role xterm * role xterm) list)
    (*State*)
    (st : state)
    (*"unification depth", which actually measures
      the number of applications of flex_rigid.*)
    (depth : int)
    (*Whether algorithm should operate extensionally*)
    (flag_ext : bool)
    (*Number of changes so far*)
    (changes : int)
    (*Previous clause in the derivation.*)
    (cl : cl_clause) =
  State.check_timeout ();
  let subststring = List.fold_right (fun (v, t) s -> (" " ^ to_string v ^ "/" ^ to_string t ^ " " ^ s)) subst "" in
    Util.sysout 3 ("\n pre_uni_new2: \n  :unilits: " ^ lit_litlist_to_protocol unilits ^ "\n  :flexlits: " ^
                     lit_litlist_to_protocol flexlits ^ "\n  :otherlits: " ^ lit_litlist_to_protocol otherlits ^
                     "\n  :subst: " ^ subststring ^ "\n  :depth: " ^ string_of_int depth ^
                     "  :flag_ext: " ^ string_of_bool flag_ext);

    if depth >= st.flags.max_uni_depth then []
    else
      match unilits with
          [] ->
            begin
              match analyze_flexflex_unilits flexlits with
                  (_, []) ->
                    (* all flex_flex, we are done *)
                    [(flexlits, otherlits, subst, changes, cl)]
                | (ff, notff) ->
                    (* start over with nonflex *)
                    pre_uni_new2 notff ff otherlits subst st depth flag_ext changes cl
            end
        | lit :: restlits when not (is_unilit lit) ->
            (* move to otherlits *)
            pre_uni_new2 restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl
        | lit :: restlits ->
            (*lit must therefore be a non-flexflex unification literal*)
            let (l, r) = uni_termpairs lit in
            let (xl, xr) = (im2xterm l, im2xterm r) in
            let xl_ty = type_of xl in
            let xr_ty = type_of xr in
            let hl = get_head_symbol xl in
            let hr = get_head_symbol xr in
            let decFuncProcessed = (lit.lit_info = getFuncOrDecTouched) 
            in
              assert (xl_ty = xr_ty);
              match (l, r, xl_ty, flag_ext, decFuncProcessed) with
                  (_, _, _, _, _) when xl = xr -> (* triv *)
                    let cl' = create_intermediate_uni_step "_triv" flexlits (otherlits @ restlits) subst st cl
                    in 
                      pre_uni_new2 restlits flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                | (Xsymbol (s, ty), _, _, _, _) when is_variable xl -> (* bind *)
                    if occurs_in st.index xr xl then []
                    else
                      let unilits' = sub (xl, xr) st restlits in
                      let flexlits' = sub (xl, xr) st flexlits in
                      let otherlits' = sub (xl, xr) st otherlits in
                      let subst' = (xl, xr) :: subst in
                      let cl' = create_intermediate_uni_step "_bind" flexlits' (otherlits' @ unilits') subst' st cl
                      in
                        pre_uni_new2 unilits' flexlits' otherlits' subst' st depth flag_ext (changes + 1) cl'
                | (_, Xsymbol (s, ty), _, _, _) when is_variable xr -> (* switch *)
                    pre_uni_new2 (switch st lit :: restlits) flexlits otherlits subst st depth flag_ext changes cl
                | (_, _, Funtype _, _, _) -> (* func *)
                    let free_vars = litlist_free_vars (unilits @ flexlits @ otherlits) in
                    let newlit = func_ext (xterm2term xl) (xterm2term xr) st free_vars in
                    let cl' = create_intermediate_uni_step "_func" flexlits (otherlits @ newlit :: restlits) subst st cl
                    in
                      pre_uni_new2 (newlit :: restlits) flexlits otherlits subst st depth flag_ext (changes + 1) cl'
                | (Xappl _, Xappl _, Basetype _, _, _) when is_variable hl && is_variable hr -> (* flexflex *)
                    pre_uni_new2 restlits (lit :: flexlits) otherlits subst st depth flag_ext changes cl
                | (Xappl _, _, Basetype _, _, _) when is_variable hl -> (* flex_rigid *) 
                    List.flatten
                      (List.map
                         (fun s ->
                            let unilits' = sub s st unilits (*This must be unilits, not restlits*) in
                            let flexlits' = sub s st flexlits in
                            let otherlits' = sub s st otherlits in
                            let subst' = s :: subst in
                            let cl' = create_intermediate_uni_step "_flex_rigid" flexlits' (otherlits' @ unilits') subst' st cl
                            in
                              pre_uni_new2 unilits' flexlits' otherlits' subst' st (depth + 1) flag_ext (changes + 1) cl')
                         (flexrigid_binding_pairs (xterm2term xl) (xterm2term xr) st))
                | (Xappl _, Xappl _, Basetype _, false, _)   (* standard dec -- no extensionality returns *)
                | (Xappl _, Xappl _, Basetype _, true, false) when hl = hr && (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) ->  
                    (* standard dec -- no extensionality returns *)
                    begin
                      match (xterm2im hl 3, xterm2im hr 3) with
                        | (Xsymbol ("|", _), Xsymbol ("|", _))
                        | (Xsymbol ("=", _), Xsymbol ("=", _)) when (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) ->
                            (* symmetry dec *)
                              let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                              let dec_lits_commuted = make_dec_lits st (List.rev (get_args xl)) (get_args xr) in
                              let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                              let dec_cl2 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits_commuted @ restlits) subst st cl
                              in
                                pre_uni_new2 (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 @
                                  pre_uni_new2 (dec_lits_commuted @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl2
                        | _  when (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) ->  (* normal dec *)
                            let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                            let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                              pre_uni_new2 (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1
                    end
                | (Xappl _, Xappl _, Basetype "$o", true, true) when hl = hr && (List.map type_of (get_args xl)) = (List.map type_of (get_args xr))  ->  
                    (* dec -- with extensionality returns *)
                    begin
                      match (xterm2im hl 3, xterm2im hr 3) with
                        | (Xsymbol ("|", _), Xsymbol ("|", _))
                        | (Xsymbol ("=", _), Xsymbol ("=", _)) ->
                            (* symmetry dec + apply bool at type $o *)
                            let (newlits1, newlits2) = bool_ext st xl xr getFuncOrDecTouched in
                            let bool_cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                            let bool_cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl in
                            let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                            let dec_lits_commuted = make_dec_lits st (List.rev (get_args xl)) (get_args xr) in
                            let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                            let dec_cl2 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits_commuted @ restlits) subst st cl
                            in
                              pre_uni_new2 restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                                pre_uni_new2 restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2 @
                                pre_uni_new2 (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 @
                                pre_uni_new2 (dec_lits_commuted @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl2
                        | _ ->  (* normal dec + apply bool at type $o *)
                            let (newlits1, newlits2) = bool_ext st xl xr lit.lit_info in
                            let bool_cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                            let bool_cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl in
                            let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                            let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                              pre_uni_new2 restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                                pre_uni_new2 restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2 @
                                pre_uni_new2 (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1
                    end
                | (Xappl _, Xappl _, Basetype _, true, true) when hl = hr && (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) ->  
                    (* dec -- with extensionality returns *)
                    begin
                      match (xterm2im hl 3, xterm2im hr 3) with
                        | (Xsymbol ("=", _), Xsymbol ("=", _)) ->
                            (* symmetry dec + return *)
                              let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                              let dec_lits_commuted = make_dec_lits st (List.rev (get_args xl)) (get_args xr) in
                              let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl in
                              let dec_cl2 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits_commuted @ restlits) subst st cl
                              in
                                pre_uni_new2 restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl @
                                  pre_uni_new2 (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 @
                                  pre_uni_new2 (dec_lits_commuted @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl2
                        | _ ->  (* normal dec + return *)
                            if (List.map type_of (get_args xl)) = (List.map type_of (get_args xr)) then
                              let dec_lits = make_dec_lits st (get_args xl) (get_args xr) in
                              let dec_cl1 = create_intermediate_uni_step "_dec" flexlits (otherlits @ dec_lits @ restlits) subst st cl 
                              in
                                pre_uni_new2 restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl @
                                  pre_uni_new2 (dec_lits @ restlits) flexlits otherlits subst st depth flag_ext (changes + 1) dec_cl1 
                            else
                              pre_uni_new2 restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl 
 
                    end
                | (_, _, Basetype "$o", true, true) -> (* apply bool *)
                    let (newlits1, newlits2) = bool_ext st xl xr lit.lit_info in
                    let bool_cl1 = create_intermediate_uni_step "_bool1" flexlits (otherlits @ newlits1 @ restlits) subst st cl in
                    let bool_cl2 = create_intermediate_uni_step "_bool2" flexlits (otherlits @ newlits2 @ restlits) subst st cl in
                      pre_uni_new2 restlits flexlits (newlits1 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl1 @
                        pre_uni_new2 restlits flexlits (newlits2 @ otherlits) subst st depth flag_ext (changes + 1) bool_cl2 
                | (_, _, Basetype _, true, true) -> (* return ext *)
                    pre_uni_new2 restlits flexlits (lit :: otherlits) subst st depth flag_ext changes cl 
                | _ -> []




(*Wrapper for Leo2's extensional pre-unification algorithm. It defines the algorithm
  internally, and only uses the algorithm if there is a unification literal in "cl";
  otherwise it returns "cl".*)
let pre_unify_new (cl : cl_clause) (st : state) =
  let litlist = Array.to_list cl.cl_litarray
  in
    if List.exists (fun l -> is_unilit l) litlist then
      let result =
        List.fold_right
          (fun (flexflexlits, otherlits, subst, changes, cl') -> fun cls ->
             if changes > 0 then
               let concluding_clause =
                 if st.flags.expand_extuni then
                   cl'
                 else
                   create_res_clause "" flexflexlits otherlits subst st cl
               in
                 concluding_clause :: cls
             else cls)
          (pre_uni_new2 litlist [] [] [] st 0 st.flags.use_extuni 0 cl)
          []
      in
	      Util.sysout 3 ("\n\ pre_uni: " ^ cl_clause_to_protocol cl ^
                         "  pre_uni_result: " ^ cl_clauselist_to_protocol result ^ "\n");
	      result
    else [cl]


let is_declit_with_boolargs (l:role lit_literal) =
  if l.lit_polarity then (false,[],[]) 
  else
    match (xterm2im l.lit_term 3) with
	Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	  let t1 = get_head_symbol (im2xterm l1) 
	  and t2 = get_head_symbol (im2xterm l2) 
	  and args1 = get_args (im2xterm l1) 
	  and args2 = get_args (im2xterm l2) in
	    if not (is_variable t1) && not (is_variable t2) && t1 = t2
	      && List.for_all (fun t -> (type_of t) = bt_o) args1
	      && List.for_all (fun t -> (type_of t) = bt_o) args2
	    then (true,args1,args2)
	    else (false,[],[])
      | _ -> (false,[],[])


(*
let pre_unify_func (cl:cl_clause) (st:state) =
  let flag = ref false in
  let rec func_neg (l:role lit_literal) =
    if l.lit_polarity then l
    else
      match (xterm2im l.lit_term 3) with
	  Xappl(Xappl(Xsymbol("=",_),l1,_),l2,_) ->
	    begin
	      match (type_of (im2xterm l1)) with
		  Funtype(_,_) -> 
		    let newlit = func_ext (xterm2term (im2xterm l1)) (xterm2term (im2xterm l2)) st cl.cl_free_vars in
		      flag := true;
		      func_neg newlit
		| _ -> l
	    end
	| _ -> l
  in
  let lits = (Array.to_list cl.cl_litarray) in
  let newlits = List.map func_neg lits in
  let result = 
    if !flag then 
      [mk_clause newlits (inc_clause_count st) cl.cl_free_vars
	 ("unify_func",[(cl.cl_number,"")],"") cl.cl_origin st]    
    else []
  in
    Util.sysout 3 ("\n\ pre_uni_func: "^(cl_clause_to_protocol cl)^"  pre_uni_func_result: "^(cl_clauselist_to_protocol result)^"\n");
    result 
*)

(*
let pre_unify_bool (cl:cl_clause) (st:state) =
  let flag = ref false in
  let bool_neg (l:role lit_literal) =
    match is_declit_with_boolargs l with
	(false,_,_) -> []
      | (true,[],[]) -> []
      | (true,args1,args2) -> flag := true; List.map2 (fun a b -> (a,b)) args1 args2 in
  let rec mk_bool_lits pairlist =
    match pairlist with
	[] -> [[]]
      | (a,b)::restpairlist -> 
	  let result = mk_bool_lits restpairlist in
	  let newres1 = List.map (fun litlist -> [(lit_mk_neg_literal a);(lit_mk_neg_literal b)]@litlist) result in
	  let newres2 = List.map (fun litlist -> [(lit_mk_pos_literal a);(lit_mk_pos_literal b)]@litlist) result in	    
	    (newres1@newres2) in
  let rec combine_results listoflists1 listoflists2 result =
    match listoflists1 with
	[] -> result
      | l::lofls -> combine_results lofls listoflists2 ((List.map (fun list -> l@list) listoflists2)@result) in
  let rec help (lits:(role lit_literal) list) =
    match lits with
	[] -> [[]]
      | lit::restlits -> 
	  let listoflitlists1 = help restlits in
	  let listoflitlists2 = 
	    let (flag,_,_) = is_declit_with_boolargs lit in
	      if flag then  mk_bool_lits (bool_neg lit) else [[lit]] in
	  let listoflitlists3 = combine_results listoflitlists1 listoflitlists2 [] in
	    listoflitlists3 in
  let clfunc = match pre_unify_func cl st with [cnew] -> cnew | _ -> cl in
  let listoflitlists = help (Array.to_list clfunc.cl_litarray) in  
  let result =
    if !flag then 
      List.map 
	(fun newlits ->  
	   mk_clause newlits (inc_clause_count st) cl.cl_free_vars
	     ("unify_bool",[(cl.cl_number,"")],"") cl.cl_origin st)
	listoflitlists
    else []
  in
    Util.sysout 3 ("\n\ pre_uni_bool: "^(cl_clause_to_protocol cl)^"  pre_uni_bool_result: "^(cl_clauselist_to_protocol result)^"\n");
    result 
*)


let pre_unify (cl:cl_clause) (st:state) = 
  pre_unify_new cl st 
  (* let res_uni = pre_unify_new cl st and
      res_func = pre_unify_func cl st and
      res_bool = pre_unify_bool cl st in
    (res_uni@res_func@res_bool)
  *)
  (* pre_unify_ext cl st) *)



(** Trivial Subsumption Rule *)

let triv_subsumes (cl1 : cl_clause) (cl2 : cl_clause) =
  let litlist1 = Array.to_list cl1.cl_litarray and
      litlist2 = Array.to_list cl2.cl_litarray in
  let res =
    (List.length litlist1 <= List.length litlist2) &&
      (List.for_all
         (fun l1 ->
            List.exists
              (fun l2 -> l1.lit_polarity = l2.lit_polarity && l1.lit_term = l2.lit_term)
              litlist2)
         litlist1)
  in
    Util.sysout 3 ("\n   " ^ cl_clause_to_protocol cl1 ^ " subsumes " ^
                     cl_clause_to_protocol cl2 ^ ": " ^ string_of_bool res);
    res


(** FO-Matching Subsumption Rule *)

let substitute_left pairlist subst st =
  List.map (fun (l, r) -> (substitute st.index l subst, r)) pairlist

let rec fo_match (termpairs:((role xterm) * (role xterm)) list) (uni:((role xterm) * (role xterm)) list) (forbiddenVars:term list) (st:state) =
  Util.sysout 3 ("\n fo_match: \n   termpairs: "^(List.fold_right (fun (v,t) s -> ("("^(to_string v)^","^(to_string t)^"),"^s)) termpairs "")^"\n   uni: "^(List.fold_right (fun (v,t) s -> ("("^(to_string v)^","^(to_string t)^"),"^s)) uni "")^"\n   forbiddenVars: "^(List.fold_right (fun (v) s -> ((Term.to_string v)^" "^s)) forbiddenVars ""));
  match termpairs with
    [] -> (true,uni)
  | (left,right)::tl ->
      match ((xterm2im left 3),(xterm2im right 3)) with 
	(Xsymbol(_,_),_) ->
	  Util.sysout 3  ("\n case 1"); 
	  if (xterm2term left) = (xterm2term right) 
	  then 
	    (Util.sysout 3 ("\n case 1a"); 
	     fo_match tl uni forbiddenVars st)
	  else
	    (Util.sysout 3 ("\n case 1b"); 
	     if is_variable left && (not (List.mem (xterm2term left) forbiddenVars))
	     then 
	       if not (occurs_in st.index right left)
	       then
		 (Util.sysout 3 ("\n case 1ba"); 
		   fo_match 
		     (substitute_left tl [(left,right)] st) 
		     (uni@[(left,right)]) 
                     forbiddenVars st)
	       else
		 (Util.sysout 3 ("\n case 1bb");  
		  (false,[]))
	     else (* is constant and not equal to r *)
	       (false,[])
	    )
      | (Xappl(_,_,_),Xappl(_,_,_)) ->
	  Util.sysout 3 ("\n case 2: "^(to_string (get_head_symbol left))^" "^(to_string (get_head_symbol right))^" "^(string_of_bool ((get_head_symbol left) = (get_head_symbol right))));
	  let head_left = (get_head_symbol left) and head_right = (get_head_symbol right) 
	  and args_left = (get_args left) and args_right = (get_args right) in
	  if (head_left = head_right) 
	      && ((type_of head_left) = (type_of head_right)) 
	      && ((type_of (List.hd args_left)) = (type_of (List.hd args_right)))
	  then
	    fo_match
	      (tl@(List.map2 (fun l r -> (l,r)) (get_args left) (get_args right)))
	      uni forbiddenVars st
	  else (* (false,[]) *)
	    if 
	      ((type_of head_left) = (type_of head_right)) 
	      && ((type_of (List.hd args_left)) = (type_of (List.hd args_right)))
	    then 
	      fo_match
		([(head_left,head_right)]@tl@(List.map2 (fun l r -> (l,r)) (get_args left) (get_args right)))
		uni forbiddenVars st
	    else (false,[])
    (*  | (Xabstr(_,_,_,_),Xabstr(_,_,_,_)) -> if alpha_equal left right st then (true,uni) else (false,[])  *)
      | (l,r) -> 
	  Util.sysout 3 ("\n case 3");
	  if (not (is_basetype (type_of (im2xterm l))))
	  then 
	    let (l',r') = (func_ext_terms (im2term l) (im2term r) st []) in
	    fo_match (tl@[((term2xterm l'),(term2xterm r'))]) uni forbiddenVars st
	  else (false,[])




let fo_match_subsumes (cl1:cl_clause) (cl2:cl_clause) (st:state) = 
  let lit_match (l1:(role lit_literal)) (l2:(role lit_literal)) (st:state) = 
    if (not (l1.lit_polarity = l2.lit_polarity)) then (false,[])
    else 
      let (flag,subst) = fo_match [(l1.lit_term,l2.lit_term)] [] cl2.cl_free_vars st in
      (flag,subst)
  in
  let rec work_off (ll1:((role lit_literal) list)) (ll2:((role lit_literal) list)) (ll2_seen:((role lit_literal) list)) (st:state) =
    Util.sysout 3 ("\n work_off: \n  ll1: "^(lit_litlist_to_protocol ll1)^"\n  ll2: "^(lit_litlist_to_protocol ll2)^"\n  ll2_seen: "^(lit_litlist_to_protocol ll2_seen));
    match ll1 with 
      [] -> true
    | hd1::tl1 -> 
	match ll2 with 
	  hd2::tl2 -> 
	    let (flag,subst) = lit_match hd1 hd2 st in
	    if flag 
	    then 
	      (work_off (List.map (fun l -> substitute_lit l st subst) tl1) (ll2@ll2_seen) [] st) ||
	      (work_off ll1 tl2 (hd2::ll2_seen) st)
	    else 
	      (work_off ll1 tl2 (hd2::ll2_seen) st)
	| [] -> false
  in
  let litlist1 = (Array.to_list cl1.cl_litarray) and
      litlist2 = (Array.to_list cl2.cl_litarray) in
  let res =
    ((List.length litlist1) <= (List.length litlist2))
    && 
      work_off litlist1 litlist2 [] st
  in Util.sysout 3 ("\n fo-match-subsumes: "^(string_of_int cl1.cl_number)^" subsumes "^(string_of_int cl2.cl_number)^"  Answer? : "^(string_of_bool res));
    res




(** Pre-Relevance-Filtering **)

let clause_consts_hashtbl = Hashtbl.create 10

let term_consts_compute st t = 
    List.filter (fun t -> is_uninterpreted_symbol st t)
       (term_symbols (xterm2term t))

let clause_consts_compute st cl =
  List.flatten 
    (List.map (fun lit -> 
    	         term_consts_compute st lit.lit_term)
       (Array.to_list cl.cl_litarray))		 
    
let get_clause_consts st cl = 
    if Hashtbl.mem clause_consts_hashtbl cl.cl_number 
    then Hashtbl.find clause_consts_hashtbl cl.cl_number 
    else 
     let consts = clause_consts_compute st cl in
       Hashtbl.add clause_consts_hashtbl cl.cl_number consts;
       consts


let rec filter_axioms_wrt_conjecture_h_1 (st:state) (axiom_clauses: cl_clause list) (conj_clauses: cl_clause list) (level:int) (result: cl_clause list) =
  Util.sysout 3 ("\n   Enter filter_axioms_wrt_conjecture_h_1 with level: "^(string_of_int level));   
  Util.sysout 3 ("\n   Conjecture clauses : ");
  List.iter (fun cl ->  Util.sysout 3 ((string_of_int cl.cl_number)^" ")) conj_clauses;
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) conj_clauses;
  Util.sysout 3 ("\n   Axiom clauses : "); 
  List.iter (fun cl ->  Util.sysout 3 ((string_of_int cl.cl_number)^" ")) axiom_clauses;
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) axiom_clauses;
  Util.sysout 3 ("\n   Result clauses : "); 		   
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) result;
  
  let difference list1 list2 =
    let res = ref [] 
    in
      (List.iter (fun entry -> 
		   if (List.mem entry !res) 
		     || (List.mem entry list2) 
		   then ()
		   else res := (entry::!res))
	list1);
      !res in

  let print_info symlist = 
    Util.sysout 3 ("[ ");  
    List.iter (fun sym ->  Util.sysout 3 (sym^" ")) symlist;
    Util.sysout 3 ("]\n") in  
    
    if level = 0 then result
    else 
      let consts_in_conj_cls = List.flatten (List.map (fun cl -> get_clause_consts st.signature cl) conj_clauses) in
      let _ = Util.sysout 3 (" consts_in_conj_cls: "); print_info consts_in_conj_cls in
      let (axiom_clauses_sharing_symbols,others) =  
	List.partition (fun cl -> 
			  let consts_in_cl = get_clause_consts st.signature cl in
			    Util.sysout 3 (" consts_in_cln "^(string_of_int cl.cl_number)^": "); 
			    print_info consts_in_cl;
			    let difference_set1 = difference consts_in_cl consts_in_conj_cls in

(*
			    and difference_set2 = difference consts_in_conj_cls  consts_in_cl in
			      Util.sysout 3 (" difference set1: "); 
			      print_info difference_set1;
			      Util.sysout 3 (" difference set2: "); 
			      print_info difference_set2;
			      
			      let max = (max (List.length difference_set1) (List.length difference_set2)) in 
*)
			     
			      let max = (List.length difference_set1) in

				(
				  max < (List.length consts_in_cl) 
			       && 
				  max <= level
			      )
		       )
	  axiom_clauses in    
	filter_axioms_wrt_conjecture_h_1 st others (axiom_clauses_sharing_symbols@conj_clauses) (level - 1) (axiom_clauses_sharing_symbols@result)

let rec filter_axioms_wrt_conjecture_h_2 (st:state) (axiom_clauses: cl_clause list) (conj_clauses: cl_clause list) (level:int) (result: cl_clause list) =
  Util.sysout 3 ("\n   Enter filter_axioms_wrt_conjecture_h_2 with level: "^(string_of_int level));   
  Util.sysout 3 ("\n   Conjecture clauses : ");
  List.iter (fun cl ->  Util.sysout 3 ((string_of_int cl.cl_number)^" ")) conj_clauses;
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) conj_clauses;
  Util.sysout 3 ("\n   Axiom clauses : "); 
  List.iter (fun cl ->  Util.sysout 3 ((string_of_int cl.cl_number)^" ")) axiom_clauses;
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) axiom_clauses;
  Util.sysout 3 ("\n   Result clauses : "); 		   
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) result;
  
  let intersection list1 list2 =
    let res = ref [] 
    in
      (List.iter (fun entry -> 
		   if (List.mem entry !res) 
		     || (not (List.mem entry list2))
		   then ()
		   else res := (entry::!res))
	 list1);
      !res in
    
  let print_info symlist = 
    Util.sysout 3 ("[ ");  
    List.iter (fun sym ->  Util.sysout 3 (sym^" ")) symlist;
    Util.sysout 3 ("]\n") in  
    
    if level = 0 then result
    else 
      let consts_in_conj_cls = List.flatten (List.map (fun cl -> get_clause_consts st.signature cl) conj_clauses) in
      let _ = Util.sysout 3 (" consts_in_conj_cls: "); print_info consts_in_conj_cls in
      let (axiom_clauses_sharing_symbols,others) =  
	List.partition (fun cl -> 
			  let consts_in_cl = get_clause_consts st.signature cl in
			    Util.sysout 3 (" consts_in_cln "^(string_of_int cl.cl_number)^": "); 
			    print_info consts_in_cl;
			    let intersection_set1 = intersection consts_in_cl consts_in_conj_cls in

(*
			    and difference_set2 = difference consts_in_conj_cls  consts_in_cl in
			      Util.sysout 3 (" difference set1: "); 
			      print_info difference_set1;
			      Util.sysout 3 (" difference set2: "); 
			      print_info difference_set2;
			      
			      let max = (max (List.length difference_set1) (List.length difference_set2)) in 
*)
			     
			      let max = (List.length intersection_set1) in

				  (0 - max) <= level
		       )
	  axiom_clauses in    
	filter_axioms_wrt_conjecture_h_2 st others (axiom_clauses_sharing_symbols@conj_clauses) (level + 1) (axiom_clauses_sharing_symbols@result)

	  
	  

	
let rec filter_axioms_wrt_conjecture (st:state) (axiom_clauses: cl_clause list) (conj_clauses: cl_clause list) (level:int) =

  Hashtbl.clear clause_consts_hashtbl;

  Util.sysout 3 ("\n Relevance Filtering with level: "^(string_of_int level)); 
  Util.sysout 3 ("\n The conjecture clauses are: ");
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) conj_clauses;
  Util.sysout 3 ("\n The axiom clauses are: "); 
  List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) axiom_clauses;
  let result =
    if level = 0 then axiom_clauses
    else 
      if level > 0 
      then 
	let res = (filter_axioms_wrt_conjecture_h_1 st axiom_clauses conj_clauses level []) in
	  if (not (axiom_clauses = [])) && (res = [])
	  then filter_axioms_wrt_conjecture st axiom_clauses conj_clauses (level + 1) 
	  else res
      else 
	let res = (filter_axioms_wrt_conjecture_h_2 st axiom_clauses conj_clauses level []) in
	  if (not (axiom_clauses = [])) && (res = [])
	  then filter_axioms_wrt_conjecture st axiom_clauses conj_clauses (level - 1) 
	  else res
  in
    Util.sysout 3 ("\n Relevance filtering is reducing the axiom clauses to: ");
    List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) result;
    result
	 




let flex_heads (clauselist:cl_clause list) (st:state) =
  let headvars = ref [] in
  let _ = 
    List.iter (fun cl -> 
		 List.iter (fun lit ->  
			      let hd = Term.get_head_symbol (xterm2term lit.lit_term) in
				if (not (Term.is_variable hd)) || (List.mem hd !headvars)
				then () 
				else headvars := (hd::!headvars))
		   (Array.to_list cl.cl_litarray))
      clauselist in

    Util.sysout 3 ("\n flex_heads applied to clause \n ");
    List.iter (fun cl ->  Util.sysout 3 ((cl_clause_to_string cl)^" ")) clauselist;
    Util.sysout 3 "\n headvars=[";
    List.iter (fun term -> Util.sysout 3 (" "^(Term.to_string term))) !headvars;
    Util.sysout 3 " ]\n";
    !headvars

let prim_subst_pairs (var:term) (st:state) = 
  let xvar = term2xterm var in
  let var_ty = Term.type_of (type_of_symbol st.signature) var in
  let var_goal_ty = bt_o in
  let var_arg_tys = all_arg_types var_ty in
    Util.sysout 3 ("\n "^(Term.to_string var)^": "^(Hol_type.to_string var_ty));
    Util.sysout 3 "\n var_arg_tys: ";
    List.iter (fun x -> (Util.sysout 3 ((Hol_type.to_string x)^" "))) var_arg_tys;
    let base_1 =			 
      [
	(xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol ctrue) [] bt_o st));
	(xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol cfalse) [] bt_o st));
	(xvar,term2xterm (imi_binding var var_arg_tys var_goal_ty (Symbol neg) [bt_o] bt_o st))
      ] in
      
    let eq_bindings = (eq_bindings var_arg_tys st) in
    let special_eq_imi_bindings =  
      (List.flatten 
	 (List.map (fun (string,tp) -> 
		      (special_eq_imi_binding var_arg_tys (Symbol string) st)) 
	    (List.filter (fun (str,tp) -> 
			    (not (Term.is_variable (Symbol str)))) 
	       (all_uninterpreted_symbols st.signature)))) in
    let base_2 = 
      (List.map (fun term -> (xvar,term2xterm term)) eq_bindings) in
      
    let base_3 = 
      (List.map (fun term -> (xvar,term2xterm term)) special_eq_imi_bindings) in
      
    let base_4 = [] in

    let result =
      match st.flags.prim_subst with
	  0 -> []
	| 1 -> base_1
	| 2 -> base_1@base_2
	| 3 -> base_1@base_2@base_3
	| 4 -> base_1@base_2@base_3@base_4
	| _ -> base_1@base_2@base_3@base_4 

    in
      result
	      
	      

let substitute_clause (pair:((role xterm) * (role xterm))) (cl:cl_clause) (st:state) =
  let _ = Util.sysout 3 ("\n substitute_clause : "^(cl_clause_to_protocol cl)^"\n") in
  match pair with
      (v,t) ->
	let literals = (Array.to_list cl.cl_litarray) in
        let old_free_vars = litlist_free_vars literals in
	if (List.mem (xterm2term v) old_free_vars)
	then 
	  (
	   let subst_literals = List.map (fun l -> substitute_lit l st [(v,t)]) literals in
	   let free_vars = litlist_free_vars subst_literals in
	   let subst_string = ("[bind("^(to_hotptp v)^",$thf("^(to_hotptp t)^"))]") in
	   let res_clause =
	    mk_clause subst_literals (inc_clause_count st) free_vars
	    	      ("prim_subst",[(cl.cl_number,subst_string)],"") cl.cl_origin st in
           let _ = Util.sysout 3 ("\n result : "^(cl_clause_to_protocol res_clause)^"\n") in
	   [res_clause]
          )
        else 
          (
           []
          )

let primsubst_new (clauselist:cl_clause list) (st:state) =
  let headvars = flex_heads clauselist st in
  let prim_subst_pairs = List.flatten (List.map (fun var -> prim_subst_pairs var st) headvars) in
  let _ = ((List.iter (fun (xvar,xterm) -> Util.sysout 3 ("\n "^(to_string xvar)^" <- "^(to_string xterm))) prim_subst_pairs);
	   Util.sysout 3 "\n") in
  let result_clauses =
    List.flatten (List.map (fun cl -> (List.flatten (List.map (fun pair -> substitute_clause pair cl st) prim_subst_pairs))) clauselist) in
  let _ = Util.sysout 3 ("\n Prim_subst_new : "^(cl_clauselist_to_protocol result_clauses)^"\n") in
    result_clauses




(** The choice rule *)


let is_skolem_term (t:term)=
  Util.sysout 3 ("\n : is_skolem_term: "^(Term.to_string t));  
  let result =
    match t with
	Symbol n -> String.contains_from n 0 's' && String.contains_from n 0 'K'
      | _ -> false in
    Util.sysout 3 ("\n : is_skolem_term_result: "^(string_of_bool result)); 
    result

let detect_choice (cl:cl_clause) (st:state) =
  Util.sysout 3 ("\n\  choice-detect: "^(cl_clause_to_protocol cl)); 
  let choice_candidate_pairs litlist =
    List.flatten
      (List.map 
	 (fun l -> 
	    if l.lit_polarity
	    then
	      match (xterm2term l.lit_term) with
		  Appl(t1,Appl(t2,t3)) -> 
		    ( match Term.type_of (type_of_symbol st.signature) t2 with
			  Funtype(Funtype(alpha,Basetype("$o")),beta) ->
			    if alpha = beta && Term.is_variable t1 && t1 = t3 
			      && (not (is_skolem_term t2))
			    then 
			      [(t1,t2)]
			    else []
			| _ -> [])
		| _ -> [] 
	    else [])
	 litlist) in 
  let choice_operators litlist candidate_pairs =
    List.flatten
      (List.map 
	 (fun l -> 
	    if l.lit_polarity
	    then []
	    else
	      List.flatten
		(List.map
		   (fun (var,choiceop) -> 
		      match (xterm2term l.lit_term) with
			  Appl(t1,t2) ->
			    if t1 = var && Term.is_variable t2
			    then [choiceop]
			    else []
			| _ -> [])
		   candidate_pairs))
	 litlist) in
  let litlist = (Array.to_list cl.cl_litarray) in
  let rec work_off choice_operators =
	match choice_operators with
	    [] -> [cl]
	  | hd::tl ->  
	      let _ = add_choice_functions st [hd] in
	      match Term.type_of (type_of_symbol st.signature) hd with
	          Funtype(Funtype(Basetype("$o"),Basetype("$o")),Basetype("$o")) ->
                    let var = create_and_insert_new_free_var (Symbol "X") (Basetype("$o")) st in
		    let lit1 = lit_mk_pos_literal st.signature (term2xterm (Appl(hd,(Abstr(var,Basetype("$o"),var))))) in
		    let lit2 = lit_mk_neg_literal st.signature (term2xterm (Appl(hd,(Abstr(var,Basetype("$o"),Appl(Symbol "~",var)))))) in
                      [
		       mk_clause [lit1] (inc_clause_count st) [] ("choiceBool",[(cl.cl_number,"")],"") cl.cl_origin st;
		       mk_clause [lit2] (inc_clause_count st) [] ("choiceBool",[(cl.cl_number,"")],"") cl.cl_origin st
		      ]
		| _ -> []
	in	      
  let result =
    if List.length litlist = 2 
    then 
      let candidatePairs = choice_candidate_pairs litlist in
      let listOfChoiceOperators = choice_operators litlist candidatePairs in
        work_off listOfChoiceOperators
    else [cl] in
    Util.sysout 3 ("\n choice-detect-result: "^(cl_clauselist_to_protocol result)); 
    result
    
let rec compress l =
    match l with
    | [] -> []
    | [_] -> l
    | h1 :: ((h2 :: _) as tail) ->
        if h1 = h2 then compress tail else h1 :: compress tail

let detect_choice_terms (cl:cl_clause) (st:state) =
   let is_choice_variable (term:term) =
     Util.sysout 3 ("\n : is_choice_variable "^(Term.to_string term));  
     let result = 
       if Term.is_variable term 
       then 
         match Term.type_of (type_of_symbol st.signature) term with
            Funtype(Funtype(alpha,Basetype("$o")),beta) -> alpha = beta 
          | _ -> false
       else false in
     Util.sysout 3 ("\n : is_choice_variable_result "^(string_of_bool result)); 
     result 
   in 
   let detect_choice_terms_lit (l:role lit_literal) =
      let rec detect_choice_term_help (term:term) (boundvars:term list) =      
         Util.sysout 3 ("\n : detect_choice_term_help "^(Term.to_string term));  
         match term with
            Symbol(_) -> []
          | Abstr(var,_,bd) -> detect_choice_term_help bd (var::boundvars)
          | Appl(hd,bd) -> 
             if List.mem hd st.choice_functions 
             then 
	       let freevars = List.map (fun v -> (Symbol v)) (Term.free_vars bd) in
	       if List.exists (fun v -> List.mem v freevars) boundvars 
               then  detect_choice_term_help bd boundvars
               else
                let _ = Util.sysout 3 ("\n :  found"^(Term.to_string bd)) in
                  (hd,hd,bd,(Term.type_of (type_of_symbol st.signature) (Appl(hd,bd))))::(detect_choice_term_help bd boundvars)
             else
               (if List.mem hd cl.cl_free_vars && is_choice_variable hd && (not (List.mem hd boundvars))
                then 
                  let choiceType = (Term.type_of (type_of_symbol st.signature) hd) in
                    ((if not (List.exists 
                              (fun choiceOp -> 
                                 let choiceOpType = (Term.type_of (type_of_symbol st.signature) choiceOp) in 
                                 let result = (choiceOpType = choiceType) in 
                                   Util.sysout 3 ("\n : compare "^(Hol_type.to_hotptp choiceOpType)^" and "^(Hol_type.to_hotptp choiceOpType)^" result "^(string_of_bool result));
                                   result)
                              st.choice_functions)
	                  then 
                            let newChoiceOp = create_and_insert_skolem_const (Symbol "Eigen") choiceType st in
                               let _ =  add_choice_functions st [newChoiceOp] in 
                               ());
                     (List.flatten
                       (List.map 
                         (fun choice -> 
                                let ty1 = Term.type_of (type_of_symbol st.signature) hd in
                                let ty2 = Term.type_of (type_of_symbol st.signature) choice in 
                                if ty1 = ty2                               
                                then 
                                   let goal_type = match ty1 with Funtype(Funtype(alpha,Basetype("$o")),beta) -> beta | _ -> raise (Failure "detect_choice_term_help") in 
                                   [(hd,choice,bd,goal_type)]  
                                else [])
                         st.choice_functions))@(detect_choice_term_help bd boundvars))
               else (detect_choice_term_help hd boundvars)@(detect_choice_term_help bd boundvars)
              )
       in
       detect_choice_term_help (xterm2term l.lit_term) []
   in 
   let candidates = (List.flatten (List.map detect_choice_terms_lit (Array.to_list cl.cl_litarray))) in
   let _ = match candidates with [] -> Util.sysout 3 ("\n : candidates empty") | _ -> Util.sysout 3 ("\n : candidates not empty") in
(*
   let rec mk_multi_exists_term (varlist:term list) (body:term) (var:term)  (ty:hol_type) = 
     match varlist with
        [] -> Appl(body,var) 
      | v::tl -> 
         let vty = (Term.type_of (type_of_symbol st.signature) v) in
           Appl(Symbol("~"),(Appl(Symbol("!"),(Abstr(v,vty,Appl(Symbol("~"),(mk_multi_exists_term tl body var ty))))))) in 
   let rec mk_multi_forall_term (varlist:term list) (body:term) (var:term)  (ty:hol_type) = 
     match varlist with
        [] -> Appl(body,var) 
      | v::tl -> 
         let vty = (Term.type_of (type_of_symbol st.signature) v) in
           Appl(Symbol("!"),Abstr(v,vty,(mk_multi_forall_term tl body var ty))) in 
*)
   match candidates with
      [] -> [cl]
    | _ -> 
      List.flatten 
       (List.map 
         (fun (hd,choice,term,ty) -> 
           let termfreevars =  List.map (fun v -> (Symbol v)) (Term.free_vars term) in
           let _ = Util.sysout 3 "\n termfreevars: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) termfreevars in 
           let termrealfreevars = List.filter (fun v -> (List.mem v cl.cl_free_vars)) termfreevars in
           let _ = Util.sysout 3 "\n termrealfreevars: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) termrealfreevars in
           let termcapturedvars = List.filter (fun v -> not (List.mem v cl.cl_free_vars)) termfreevars in
           let _ = Util.sysout 3 "\n termcapturedvars: "; List.iter (fun x -> (Util.sysout 3 ((Term.to_string x)^" "))) termcapturedvars in
	   let var = create_and_insert_new_free_var_with_simple_name ty st in
           let choiceAxInst = (Appl(Appl(Symbol("|"),(Appl(Symbol("~"),(Appl(Symbol("~"),(Appl(Symbol("!"),(Abstr(var,ty,(Appl(Symbol("~"),(Appl(term,var))))))))))))),(Appl(term,(Appl(choice,term)))))) in
           let lit1 = (lit_mk_pos_literal st.signature (term2xterm (beta_normalize choiceAxInst))) in 
		 match (termcapturedvars,(hd = choice))  with
                     ([],true) ->  let cl2new = rename_free_variables (mk_clause [lit1] (inc_clause_count st) termrealfreevars ("choice",[(cl.cl_number,"")],"") cl.cl_origin st) st in
                                     [cl;cl2new]
                   | ([],false) -> (* let cl1new = cl in *)
  		                   let cl2new = instantiate [(term2xterm hd,term2xterm choice)] cl st in
                                   let cl3new = rename_free_variables (mk_clause [lit1] (inc_clause_count st) termrealfreevars ("choice",[(cl.cl_number,"")],"") cl.cl_origin st) st in
                                     [cl;cl2new;cl3new]
                   | (_,_) ->     [cl] 
				     
(*
                   | (_,true) -> let cl1new = cl in 
		                  let cl2new = rename_free_variables (mk_clause [lit1] (inc_clause_count st) termrealfreevars ("choice",[(cl.cl_number,"")],"") cl.cl_origin st) st in
                                  let cl3new = rename_free_variables (mk_clause [lit2] (inc_clause_count st) termrealfreevars ("choice",[(cl.cl_number,"")],"") cl.cl_origin st) st in
                                     [cl1new;cl2new;cl3new]
                   | (_,false) -> (* let cl1new = cl in *)
                                 let cl2new = instantiate [(term2xterm hd,term2xterm choice)] cl st in
		                 let cl3new = rename_free_variables (mk_clause [lit1] (inc_clause_count st) termrealfreevars ("choice",[(cl.cl_number,"")],"") cl.cl_origin st) st in
                                 let cl4new = rename_free_variables (mk_clause [lit2] (inc_clause_count st) termrealfreevars ("choice",[(cl.cl_number,"")],"") cl.cl_origin st) st in
                                     [cl2new;cl3new;cl4new]
*)
         )
         candidates)




(* Choice is a rule that has been added to extensional unification; here we simply call pre_unify_ext for th *)

(*
let apply_choice (cl:cl_clause) (st:state) = 
  let count = st.clause_count in 
  let result = pre_unify cl st in
    if st.clause_count > count
    then result
    else []
*)

let apply_choice (cl:cl_clause) (st:state) =  
   Util.sysout 3 ("\n apply-choice: "^(cl_clause_to_protocol cl)); 
   let result = detect_choice_terms (cl:cl_clause) (st:state) in
     Util.sysout 3 ("\n apply-choice-result: "^(cl_clauselist_to_protocol result)); 
     result

