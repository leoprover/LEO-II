(*Implements monotonicity analyses based on SAT encoding,
  as described in the paper "Sort it out with monotonicity" by Claessen et al (2011)*)

open General
open Translation_general
open Hol_type
open App_term
open Af
open State

exception MONOTONICITY of string


(* Conversion to CNF *)

let rec push_neg ta =
  match ta with
      App (Const ("~", ty_o1),
           [App (Const (op, ty_o2), tas)]) when op = "&" || op = "|" ->
        let op' = if op = "&" then "|" else "&"
        in
          App (Const (op', ty_o2),
               List.map (fun ta' ->
                           App (Const ("~", ty_o1), [ta'])
                           |> push_neg)
                 tas)
    | App (Const ("~", ty_o1), [Quant (qtfr, vars, ta')]) ->
        let qtfr' = if qtfr = "!" then "?" else "!"
        in
          Quant (qtfr', vars,
                 App (Const ("~", ty_o1), [ta'])
                 |> push_neg)
    | App (ta1, tas) -> App (push_neg ta1, List.map push_neg tas)
    | Quant (qtfr, vars, ta') -> Quant (qtfr, vars, push_neg ta')
    | Abs (_, _) -> raise (MONOTONICITY "Illegal term")
    | _ -> ta

let rec double_neg ta =
  match ta with
      App (Const ("~", _), [App (Const ("~", _), [ta'])]) -> double_neg ta'
    | App (ta1, tas) -> App (double_neg ta1, List.map double_neg tas)
    | Quant (qtfr, vars, ta') -> Quant (qtfr, vars, double_neg ta')
    | Abs (_, _) -> raise (MONOTONICITY "Illegal term")
    | _ -> ta

let nnf ta =
  let prev_ta = ref ta in
  let invar = ref true
  in
    while !invar do
      let ta' =
        !prev_ta
        |> double_neg
        |> push_neg
      in
        invar := ta' <> !prev_ta;
        prev_ta := ta'
    done;
    !prev_ta

let rec expand_defs ta =
  match ta with
      Var _ -> ta
    | Const _ -> ta
    | App (Const ("=>", _), [ta1; ta2]) ->
        Const ("|", dummy_type(*FIXME*)) $$
          [(Const ("~", dummy_type(*FIXME*)) $$ [expand_defs ta1]);
           expand_defs ta2]
    | App (Const ("<=>", _), [ta1; ta2]) ->
        Const ("&", dummy_type(*FIXME*)) $$
          [expand_defs (Const ("=>", dummy_type(*FIXME*)) $$ [ta1; ta2]);
           expand_defs (Const ("=>", dummy_type(*FIXME*)) $$ [ta2; ta1])]
    | App (ta1, tas) -> App (expand_defs ta1, List.map expand_defs tas)
    | Quant (qtfr, vars, ta') -> Quant (qtfr, vars, expand_defs ta')
    | Abs (_, _) -> raise (MONOTONICITY "Illegal term")

let rec flatten ta =
  let c_pred c =
    function
        (App (Const (c', _), _)) when c' = c -> true
      | _ -> false in
  let get_capp_tas c =
    function
        App (Const (c', _), tas) when c' = c -> tas
      | _ -> []
  in
    match ta with
      App (Const ("&" as c, _), tas)
    | App (Const ("|" as c, _), tas) ->
        let (same, others) = List.partition (c_pred c) tas
        in
          if same = [] then ta
          else
            let lifted_tas = List.map (get_capp_tas c) same |> List.concat
            in
              App (Const (c, dummy_type), lifted_tas @ others)
              |> flatten
    | Quant (quant, vars, ta') -> Quant (quant, vars, flatten ta')
    | App (ta1, tas) -> App (flatten ta1, List.map flatten tas)
    | _ -> ta

let rec naive_distrib ta =
  match ta with
      App (Const ("|", _), tas) ->
        let and_pred = function (App (Const ("&", _), _)) -> true | _ -> false in
        let (ands, others) = List.partition and_pred tas
        in
          if ands = [] then App (Const ("|", dummy_type), List.map naive_distrib tas)
          else
            let hd_conjuncts =
              List.hd ands
              |> function App (Const ("&", _), conjs) -> conjs
                          | _ -> raise (MONOTONICITY "Bad term") in
            let rest = others @ List.tl ands in
              if rest = [] then App (Const ("&", dummy_type), List.map naive_distrib hd_conjuncts)
              else
                Const ("&", dummy_type) $$
                  (List.map
                     (fun disjunct ->
                        (List.map
                           (fun conjunct ->
                              Const ("|", dummy_type) $$ [conjunct; disjunct])
                           hd_conjuncts))
                     rest
                  |> List.concat)
                  |> naive_distrib
    | App (Const ("&", ty), tas) -> App (Const ("&", ty), List.map naive_distrib tas)
    | Quant (qtfr, vars, ta') -> Quant (qtfr, vars, naive_distrib ta')
    | _ -> ta

let next_sK = ref 0
let get_next_sK () =
  let next_num = !next_sK
  in
    next_sK := 1 + !next_sK;
    "skol" ^ string_of_int next_num

let rec skolemize allVar subst ta =
  match ta with
      Var (s, _) ->
        if List.mem_assoc s subst then
          List.assoc s subst
        else ta
    | Const _ -> ta
    | App (ta1, tas) -> App (skolemize allVar subst ta1, List.map (skolemize allVar subst) tas)
    | Quant (qtfr, vars, ta') ->
        if qtfr = "!" then
          skolemize (List.map (fun (s, ty) -> Var (s, ty)) vars @ allVar) subst ta'
        else
          let skolems = List.map (fun (s, _) -> (s, Const (get_next_sK (), dummy_type) $$ allVar)) vars
          in skolemize allVar (skolems @ subst) ta'
    | _ -> raise (MONOTONICITY "Unexpected case")

let appterm_cnf =
  expand_defs
  @> nnf
  @> skolemize [] []
  @> (fun ta ->
        let prev_ta = ref ta in
        let invar = ref true
        in
          while !invar do
            let ta' =
              !prev_ta
              |> flatten
              |> naive_distrib
            in
              invar := ta' <> !prev_ta;
              prev_ta := ta'
          done;
          !prev_ta)


(* Generation of SAT problem *)

type sublit_t =
    T of string * sublit_t list
  | V of string * hol_type
type literal = bool * (string * sublit_t list)
type cnf = literal list list

(*Map from predicate names to int.
  Latter is > 2 for uninterpreted predicates.
  Mapping convention:
   "true" is mapped to 0 and 2,
   "false" is mapped to 1.
  Each predicate is reserved two consecutive numbers.
   It's odd number denotes "predicate = true",
   and the even number "predicate = false"*)
let next_pred_no = ref 3
let get_next_pred_no () =
  let next_num = !next_pred_no
  in
    next_pred_no := 2 + next_num;
    next_num
let pred_dict : (string * int) list ref = ref []
let get_pred_id s =
  if List.mem_assoc s !pred_dict then
    List.assoc s !pred_dict
  else
    let s_n = get_next_pred_no ()
    in
      pred_dict := (s, s_n) :: !pred_dict;
      s_n

(*List of "guards" predicates, ordered by clause and literal.
  Uses mapping convention described above to map the p_True and p_False letters*)
let guards : (string * int) list list list option ref = ref None
(*List of guards predicates, corresponding to list of literals in a clause.
  Convention: if a variable isn't defined in a guard, then it's false*)
let guards_l : (string * int) list list option ref = ref None
(*Current guard predicate being built (i.e. for current literal).
  A guard indicates, for a specific literal, the guarded status of a variable.
  The variable is represented as a string, and the status as an integer*)
let guard : (string * int) list ref = ref []

let rec apptermCNF_to_cnf_literal p_n ta : sublit_t =
  match ta with
      Var (s, ty) ->
        begin
          match p_n with
              None -> ()
            | Some p_id ->
                if List.mem_assoc s !guard then
                  IFDEF DEBUG THEN
                    assert(p_id = List.assoc s !guard)
                  END
                else
                  guard := (s, p_id) :: !guard
        end;
        V (s, ty)
    | Const (s, _) -> T (s, [])
    | App (Var (_, _) as v, tas) ->
        (*V(...) is actually appK(V, ...), where it doesn't matter
          if "..." contains variables (since they'll appear within an appK*)
         T (appK, [apptermCNF_to_cnf_literal None v]) (*CHECK ignore "tas"?*)
    | App (Const (s, ty), tas) -> T (s, List.map (apptermCNF_to_cnf_literal None) tas)
    | App (App (_, _), _) -> T (appK, [])
    | _ -> raise (APP_TERM ("Unexpected term form", ta))

let rec apptermCNF_to_cnf_disj ta : literal list =
  let add_guard pol c tas =
        if !guards_l = None then
          guards_l := Some []
        else
          guards_l := Some (!guard :: the !guards_l);
        guard := [];
        let p_id =
          if c = "=" then
            if pol then 1 else 0
          else 1 + get_pred_id c
        in [(pol, (c, List.map (apptermCNF_to_cnf_literal (Some p_id)) tas))]
  in
  match ta with
      App (Const ("|", _), tas) ->
        List.map apptermCNF_to_cnf_disj tas
        |> List.concat
    (*some bad cases*)
    | Quant (_, _, _) (*quantifiers should have been removed*)
    | App (Const ("&", _), _) (*ta cannot be conjunctive*) ->
        raise (APP_TERM ("Such a term should not be here", ta))
    (*negative literals*)
    | App (Const ("~", _), [Const (c, _)]) ->
        IFDEF DEBUG THEN
          (*nullary predicate -- can't be equality*)
          assert (c <> "=")
        END;
        add_guard false c []
    | App (Const ("~", _), [App (Const (c, _), tas)]) ->
        add_guard false c tas
    | App (Const ("~", _), [Var (_, _) as ta']) ->
        (*note unwritten pK guard*)
        add_guard false pK [ta']
    | App (Const ("~", _), [App (Var (_, _), tas)]) ->
        (*here we have a pK applied to a appK,
          so there are no toplevel variables*)
        add_guard false pK []
    | App (Const ("~", _), [App (App (_, _), tas)]) ->
        (*can ignore first argument since it'll be wrapped in an appK, but there
          might be variables in "tas"*)
        add_guard false appK tas
    (*positive literals*)
    | Const (c, _) ->
        IFDEF DEBUG THEN
          (*nullary predicate -- can't be equality*)
          assert (c <> "=")
        END;
        add_guard true c []
    | App (Const (c, _), tas) ->
        add_guard true c tas
    | Var (_, _) ->
        (*note unwritten pK guard*)
        add_guard true pK [ta]
    | App (Var (c, _), tas) ->
        (*here we have a pK applied to a appK,
          so there are no toplevel variables*)
        add_guard true pK []
    | App (App (_, _), tas) ->
        (*can ignore first argument since it'll be wrapped in an appK, but there
          might be variables in "tas"*)
        add_guard true appK tas
    (*remaining bad cases*)
    | _ ->
        raise (APP_TERM ("Unexpected term form", ta))

let rec apptermCNF_to_cnf (ta : app_term) : cnf =
  match ta with
      App (Const ("&", _), tas) ->
        List.map apptermCNF_to_cnf tas
        |> List.concat
    | Quant (_, _, _) ->
        raise (APP_TERM ("Such a term should not be here", ta))
    | _ ->
        (*start working on a clause*)
        if !guards = None then
          guards := Some []
        else
          guards := Some (the !guards_l :: the !guards);
        guards_l := None;
        [apptermCNF_to_cnf_disj ta]

(*Produces propositional problem to send to Minisat. Type is monotonic
  in original problem iff this propositional problem is SAT*)
let monotone_sat (clauses : cnf) ty =
  (*returns a SAT clause which encodes the "safe" proposition*)
  let safe clause_idx ty t : int list =
    match t with
        V (s, s_ty) when s_ty = ty ->
          (*FIXME could optimise by removing "false" literals, and by setting whole clause to "true" when one of its literals is "true"*)
          List.map
            (fun guard_assoc ->
               if List.mem_assoc s guard_assoc then List.assoc s guard_assoc
               else 1(*i.e. false*))
            (List.nth (the !guards) clause_idx) (*guard predicates for clause_idx, ordered by literal*)
      | _ -> [0] (*i.e. true*) in
  let either_or =
    List.map
      (fun (_, p_true) ->
         [- p_true; - (p_true + 1)])
      !pred_dict in
  let monoclause cl_idx clause =
    List.fold_left
      (fun (list, l_idx) (pol, (pred, args)) ->
         let result =
           match (pol, pred) with
               (true, "=")
             | (false, "!=") ->
                 begin
                   match args with
                       [t1; t2] -> safe cl_idx ty t1 :: safe cl_idx ty t2 :: list
                     | _ -> raise (MONOTONICITY "Unexpected case")
                 end
             | (true, "!=")
             | (false, "=") -> list (*i.e. true*)
             | _ ->
                 let p = ~- (?! pol ((+) 1) (get_pred_id pred)) in
                 (*set of clauses corresponding to each arg*)
                 let safe_clauses = List.map (safe cl_idx ty) args
                 in List.map (fun sat_clause -> p :: sat_clause) safe_clauses @ list
         in (result, l_idx + 1))
      ([], 0(*literal index*)) (*this will represent a set of SAT clauses*)
      clause |> fst in
  let monoclauses =
    List.fold_left
      (fun (list, cl_idx) clause ->
         let result = monoclause cl_idx clause @ list
         in (result, cl_idx + 1))
      ([], 0(*clause index*))
      clauses |> fst
  in
    (*Get segfault if all clauses are singleton*)
    [[0;2];[2]] @ [[-1]] @ either_or @ monoclauses

let appterm_to_minisatProblem =
  appterm_cnf
  @> apptermCNF_to_cnf
  @> (fun f ->
        let guard_lit_pred =
          match !guards_l with
              None -> []
            | Some guard_lit -> guard_lit in
        let guards_clause_pred =
          match !guards with
              None -> []
            | Some guard_clauses -> guard_clauses
        in
          (guards := Some (guard_lit_pred :: guards_clause_pred));
          f)
  @> monotone_sat


(* Main *)

(*
let prob = conjoin whole problem
foreach basetype ty
  let sat = appterm_to_minisatProblem prob ty
  monotone iff minisat sat
lift to function types
*)
let analysis (st : State.state) : (string * af) list -> decoration_pred = fun clauses ->
  guards := None;
  guards_l := None;
  guard := [];
  let clauses' =
    List.map snd clauses
    |> get_af_formulas (fun x -> x <> Proxy) in
  let minisat_prob =
    App (Const ("&", dummy_type), clauses')
    |> appterm_to_minisatProblem in
  let check_mono_of ty =
    let prob = minisat_prob ty in
      IFDEF DEBUG THEN
        Util.sysout 1 ("\nChecking " ^ Hol_type.to_string ty ^
                         "; clauses = " ^ string_of_int (List.length prob));
      END;
      Minisatinterface.minisat_init (10 (* List.length !pred_dict *));
      List.iter
        (fun cl ->
           List.iter Minisatinterface.minisat_addLit cl;
           ignore(Minisatinterface.minisat_addClause ()))
        prob;
      let result = Minisatinterface.minisat_search () in
        IFDEF DEBUG THEN
          Util.sysout 1 ("; mono=" ^ string_of_bool result);
        END;
        result in
  let types =
    Signature.all_fixed_basetypes st.signature
    |> (List.filter
          (fun x ->
             x <> Signature.bt_type &&
               (*$o should never be monotonic*)
               x <> Signature.bt_o)) in
  let basetypes_pred =
    List.fold_left
      (fun pred ty ->
         if check_mono_of ty then
           fun ty' ->
             if ty' = ty then false else pred ty'
         else
           fun ty' ->
             if ty' = ty then true else pred ty')
      (fun _ -> true)
      types in
  (*lift basetypes_pred to functions*)
  let rec pred ty =
    match ty with
        Basetype s -> basetypes_pred ty
      | Funtype (ty1, ty2) ->
          true
          (*FIXME this is crude. A better improvement would be to
                  analyse function types in a way similar to the
                  analysis done in basetypes_pred*)
  in pred
