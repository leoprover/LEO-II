
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

let ratio_strategy cl1 cl2 =
  (*FIXME the Set_of_clauses structure can currently only be reliably used with
          age-based clause ordering -- otherwise the prover will be incomplete*)
  age_order cl1 cl2
  (* if next_ratio () = 0 then age_order cl1 cl2 else Clause.cl_compare cl1 cl2 *)

(*FIXME this is a hook for the clause comparison function. Previously we used
        to use Clause.cl_compare but this had completeness issues. Using the
        ratio strategy should improve this.
        Currently we don't actually need this to be a hook, since the user
        cannot influence clause selection*)
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
