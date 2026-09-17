
let ratio = 4
let ratio_mod = ref 0
let next_ratio () =
  ratio_mod := (!ratio_mod + 1) mod ratio;
  !ratio_mod

(*FIXME put in general*)
let int_compare x y =
  if x < y then -1
  else if x = y then 0
  else 1

let age_order cl1 cl2 = int_compare cl1.Clause.cl_number cl2.Clause.cl_number

(* The set is ordered by clause number, and by nothing else.  Clause numbers
   are unique, so membership and removal are exact.  An order that can call two
   distinct clauses equal -- comparing weights, say -- makes the set drop
   clauses silently, which is where the completeness problem recorded here
   until 1.7 came from.

   Which clause to work on next is a different question, and is answered by
   `select` below rather than by the set's own order. *)
let ratio_strategy cl1 cl2 = age_order cl1 cl2

let clause_selection : (Clause.cl_clause -> Clause.cl_clause -> int) ref =
  ref ratio_strategy

module Set_of_clauses =
  Set.Make
    (struct
       type t = Clause.cl_clause
       let compare = (fun cl1 cl2 -> !clause_selection cl1 cl2)
     end)

let cl_clauseset_to_string (cll : Set_of_clauses.t) =
  "[" ^ Set_of_clauses.fold (fun i s -> s ^ Clause.cl_clause_to_string i) cll "" ^ "]"

let list_to_set (cll : Clause.cl_clause list) =
  List.fold_left (fun s c -> Set_of_clauses.add c s)
    Set_of_clauses.empty cll

(* ---------------------------------------------------------------------- *)
(* Given-clause selection                                                 *)
(* ---------------------------------------------------------------------- *)

(* Lighter clauses first, with ties broken by age.  The weight is the one the
   clause was built with, from the term weight in Orderings.weighting_hook. *)
let weight_order cl1 cl2 =
  let w1 = cl1.Clause.cl_size and w2 = cl2.Clause.cl_size in
    if w1 <> w2 then int_compare w1 w2 else age_order cl1 cl2

(* One clause is taken by age in every `age_weight_ratio` selections, the rest
   by weight.  Selecting only by weight starves a heavy clause indefinitely and
   loses the fairness that completeness rests on; selecting only by age is
   first in first out, which is what LEO-II did up to 1.7.  Set it to 1 to
   recover that behaviour. *)
let age_weight_ratio = ref 5
let selections = ref 0

let select (set : Set_of_clauses.t) =
  let oldest = Set_of_clauses.min_elt set in
    incr selections;
    if !age_weight_ratio <= 1 || !selections mod !age_weight_ratio = 0 then oldest
    else
      Set_of_clauses.fold
        (fun cl best -> if weight_order cl best < 0 then cl else best)
        set oldest
