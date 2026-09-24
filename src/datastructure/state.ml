(* Configuration and state-related structures used by LEO-II

FIXME strings being used in various places,
      e.g configuration.foatp, input_logic, etc
*)

open List
open Util
open Term
open Termset
open Termsystem
open Signature
open Literal
open Clause
open Clauseset
open Hol_type


(*
indicates what status Leo-II should return in case of a given outcome.
Axioms but no conjecture : Unsatisfiable/Satisfiable
(Axioms and) conjecture : Theorem/CounterSatisfiable

(Note that for no axioms and no conjecture : Tautology)
*)
type operating_mode =
    Unsatisfiable_vs_Satisfiable
  | Theorem_vs_CounterSatisfiable

type schedule =
  {duration : float;
   strategy : string list;
  }

(*Leo-II's configuration record*)
type configuration = {
  mutable foatp : string;
  mutable dir : string;
  mutable interactive : bool;
  mutable time_slices : int;
  mutable global_timeout : int;
  schedules : schedule Queue.t;
  mutable debug : int;
  mutable problemfiles : string list;
  mutable operating_mode : operating_mode;
  (*if None then use the strategy schedule's, otherwise force this timeout value*)
  mutable atp_timeout_forced : int option;
  mutable analyze : bool;
}

(*Leo-II's default initial config*)
let global_conf : configuration = {
  foatp = "e";
  dir = "";
  interactive = false;
  time_slices = 4;
  debug = 1;
  problemfiles = [];
  schedules = Queue.create ();
  global_timeout = 600;
  operating_mode = Theorem_vs_CounterSatisfiable;
  atp_timeout_forced = None;
  analyze = false
}

let current_schedule = ref {duration = 0.0; strategy = []} (*overwritten at start of each slice*)
let child_time = ref 0.0 (*reset at start of each slice*)
(*the cumulative systime (including external ATP time) before the current problem was started*)
let sys_time_offset = ref 0.0
(*cumulative time spent solving current problem*)
let problem_cumulative_time = ref 0.0
(*accumulates, per problem, the overshooting of duration per slice. we try to win this back
  gradually along the slices, and altogether at the last slice*)
let problem_overshot = ref 0.0
let schedule_start = ref 0.0

(*When the whole run must be over, set from -t before anything is read.  The
  slice deadline cannot cover the work that happens before the first slice
  exists -- reading the problem and indexing it, which on a problem with deep
  terms takes minutes -- and that work is what made "-t 10" end the run
  neither at ten seconds nor at all.*)
let global_deadline = ref 0.0

exception STRATEGY_TERMINATED

(*The clock the budgets are measured on.

  Measured on the wall clock, the outcome of a run depends on what else the
  machine is doing.  The slices and the limit handed to the first-order prover
  are computed from the time left, and under load that time runs out while the
  work done does not grow with it, so the same problem is proved on a quiet
  machine and missed on a busy one.  Measured on the 294 problems of the
  ontological-argument dataset, two of them fell on either side of the limit
  from one run to the next: ScottVariantHOMLAndersonQuant/Pos five times out of
  ten, always at 5.9 seconds, and GoedelVariantHOML3AndersonQuant/Th4 once and
  then not again.

  Unix.times counts the CPU seconds this process has used and those of the
  children it has waited for.  The first-order prover is run synchronously and
  reaped, so its seconds are in there, and a budget measured this way buys the
  same amount of work on any machine.  The first-order prover is itself given a
  CPU limit rather than a wall-clock one, so with this the whole budget is one
  kind of second throughout.

  What this costs: a run can now take longer in wall-clock terms than the limit
  says, by whatever factor the machine is oversubscribed.  The real-time alarm
  in leo.ml is the backstop against a hang and is set wide enough to allow it.*)
let cpu_time () =
  let t = Unix.times () in
    t.Unix.tms_utime +. t.Unix.tms_stime +. t.Unix.tms_cutime +. t.Unix.tms_cstime

(*time left for this schedule*)
let time_remaining_of_schedule () = !schedule_start -. cpu_time ()

(*FIXME min. time slices for each strategy could go in schedule record, instead of having it constant*)
let atp_subslices = 5

(*The floor under the time given to one call of the first-order prover.

  Raising this to 2 was tried and rejected.  On the 46 problems of the
  ontological-argument set that E alone solves in under a second and LEO-II
  does not solve at all in ten, a floor of one second solves none and a floor
  of two solves five, which looked like a clear gain.  It was not: measured
  over all 294 problems the floor of two scores 166 and 167 against 168 for
  the floor of one.  The gain was an artefact of measuring only on problems
  the default already fails, where a change can win but never lose.*)
let atp_min_timeout = 1

(*The shortest slice worth creating.  This used to be the ATP floor times the
  number of calls a slice schedules, which ties two independent decisions
  together: changing the floor then also changes how many strategies get to
  run, and a measurement of the one is confounded by the other.  Five seconds
  is where a slice still carries a strategy; at the current floor this is the
  same number as before, so the behaviour is unchanged.*)
let min_slice_seconds = 5

(*raises STRATEGY_TERMINATED if timeout for current schedule has expired*)
let check_timeout () =
  if not global_conf.interactive then
    begin
      if Build_config.debug then
        begin
          Util.sysoutf 2 (fun () -> ("check_timeout: cpu=" ^ string_of_float (cpu_time ()) ^
          " e=" ^ string_of_float !child_time ^
          " pct=" ^ string_of_float !problem_cumulative_time ^ "\n"));
          Util.sysoutf 2 (fun () -> ("time_left: " ^ string_of_float (time_remaining_of_schedule ()) ^ "\n"))
        end;
      (*No schedule, no deadline.  schedule_start is the absolute time a slice
        must end by, and it is zero until a slice is created, which makes the
        remaining time hugely negative.  Callers that run before the first
        slice -- reading the problem, choosing the strategies -- would then be
        cut off at once.  Only a schedule that exists can expire.*)
      (*FIXME make the "0.1" constant a parameter?*)
      if (!global_deadline > 0.0 && cpu_time () > !global_deadline)
         || (!schedule_start > 0.0 && time_remaining_of_schedule () -. 0.1 < 0.)
      then raise STRATEGY_TERMINATED
    end

type szs_status =
    CounterSatisfiable | Error | Force | GaveUp | ResourceOut
  | Satisfiable | Tautology | Theorem | Timeout| Unknown | Unsatisfiable | User
let szs_status_string = function
    CounterSatisfiable -> "CounterSatisfiable"
  | Error -> "Error"
  | Force -> "Force"
  | GaveUp -> "GaveUp"
  | ResourceOut -> "ResourceOut"
  | Satisfiable -> "Satisfiable"
  | Tautology -> "Tautology"
  | Theorem -> "Theorem"
  | Timeout -> "Timeout"
  | Unknown -> "Unknown"
  | Unsatisfiable -> "Unsatisfiable"
  | User -> "User"

(*maps SZS status into an int for use as an exit code.
  It orders SZS status in terms of gravity*)
let szs_status_exitcode = function
  (*"ok" status*)
    Theorem -> 0
  | Unsatisfiable -> 1
  | Timeout -> 2
  | ResourceOut -> 3
  | GaveUp -> 4
  | CounterSatisfiable -> 5
  | Satisfiable -> 6
  | Tautology -> 7
  (*externally-forced status*)
  | User -> 50
  | Force -> 51
  (*"strange" status*)
  | Unknown -> 126
  | Error -> 127


(** Misc state **)

let current_problem_file = ref ""

(*Question answering.  A formula of role "question" asks for the instances of
  its existential variables.  LEO-II proves it like a conjecture; the instances
  come back from the first-order prover, which is given the clauses of the
  question as a question of its own, and are reported beside the status.*)
let question_posed = ref false
let question_answers : string list ref = ref []

(** Logic being processed by Leo-II **)

let input_logic : string list ref = ref []

let get_input_logic () = !input_logic

let set_input_logic l =
  if not (List.mem l !input_logic) then
    input_logic := l :: !input_logic

let is_an_input_logic l =
  List.mem l !input_logic

let reset_input_logic () =
  input_logic := []


(** Flag and state structures **)

(*Type of LEO-II flags*)
type flags = {
    mutable verbose : bool;
    mutable max_clause_count : int;
    mutable max_loop_count : int;
    mutable max_uni_depth : int;
    mutable write_protocol_files : bool;
    mutable write_fo_like_clauses : bool;
    mutable pretty_print_only : bool;
    mutable fo_translation : string;
    (*Call the first-order prover every N iterations of the main loop.

      This was 1 -- after every single iteration -- and that starves the
      higher-order search that the first-order prover depends on.  Each call
      costs the whole second a time slice allows it, so on a ten second limit
      ten calls exhaust the budget; on QUA006^1 the loop then ran *no*
      iterations at all, and every one of those ten calls answered GaveUp,
      meaning it saturated: the clauses a refutation needs had not been
      derived yet, because deriving them is what the calls were preventing.

      Measured at 5: 205 of the 294 ontological-argument problems against 180
      at 1, and 332 of 400 small TH0 theorems drawn across the TPTP against
      326.  Neither 3 (194 and there) nor 20 (198) does as well, and 20 spends
      so long between calls that three quarters of the failures become
      timeouts rather than an honest answer.*)
    mutable atp_calls_frequency : int;
    mutable atp_prover : string;
    mutable atp_timeout : int;
    mutable proof_output : int;
    mutable protocol_output : bool;
    mutable prim_subst : int;
    mutable unfold_defs_early : bool;
    (*Give a definition to the search as an equation, rather than replacing
      every occurrence of the symbol by its body.  Unfolding is what LEO-II
      has always done, and it is what makes the terms of a modal embedding
      enormous: on GoedelVariantHOML3 the problem handed to the first-order
      prover reaches 868KB, which that prover cannot read in a minute.
      Vukmirovic et al., "Making Higher-Order Superposition Work", measure
      the opposite on the TPTP as a whole: rewriting the definitions away in
      preprocessing proves 1635 problems, leaving them as plain equations
      1298.  Their benchmark is not ours -- the modal embeddings here are the
      case their Example 2 singles out -- so this is a flag, not a default.*)
    mutable defs_as_rules : bool;
    (*Upper bound on how many clauses one call to the first-order prover is
      given; 0 means "all of them", which is what Leo-II has always done.
      A saturating prover handed 25000 clauses reads them and little else,
      so past a few hundred the call is wasted.  Cutting the set down is
      sound -- a refutation from a subset is a refutation -- and only the
      cooperation's completeness suffers, which the next call repairs.*)
    mutable atp_max_clauses : int;
    (*How many of the problem's own lambda abstractions a universal variable
      of matching type is instantiated with, over and above the free variable
      it is otherwise replaced by; 0 turns the rule off.

      The instantiation a hard problem needs is often written in the problem.
      GoedelVariantHOML3/NegProps conjectures that neither the empty property
      nor "^[X]: X != X" is positive, and both abstractions stand in the
      conjecture; .../L conjectures that being God-like is positive, and the
      property it must instantiate with is the body of the definition of g.
      Primitive substitution cannot reach either: it assembles bindings out of
      connectives and quantifiers, never out of the problem's terms.  The same
      shape recurs in Cantor's theorem, where the binding is the diagonal.

      It fires once, between the first normalisation and the main loop.  Not
      earlier: a clause is implicitly universally closed, so the variables an
      axiom is stated with only become free variables when the clause exists.
      Not later: by then the main loop has copied them into everything it has
      derived, and an instance there reaches one clause of a family.  And not
      at the quantifier during normalisation, which was tried -- normalising
      runs to a fixpoint, every instance offers the same quantifier again, and
      on GoedelVariantHOML3/NegProps the rule fired ten thousand times.

      Measured on the 294 ontological-argument problems at ten seconds, and it
      loses: with "-ns" 174 without it, 166 at 1, 142 at 2, 139 at 4; from the
      plain configuration 180, 170 and 142; from the strongest portfolio
      branch 135 and 101.  Not one of those configurations answers a problem
      the portfolio does not already answer.  The technique is Vukmirovic et
      al.'s Boolean instantiation and it earns its keep across the TPTP, where
      a problem is small and needs one hard instantiation; these problems are
      the other shape, many axioms over a tiny signature, and multiplying that
      clause set buries the one term that would help.  Off by default, and it
      does not belong in a portfolio branch.*)
    mutable instantiate_max : int;
    mutable relevance_filter : int;
    (*tolerance for new symbols in one round; -1 means "use the level"*)
    mutable relevance_tolerance : int;
    mutable replace_leibnizEQ : bool;
    mutable replace_andrewsEQ : bool;
    mutable use_choice : bool;
    mutable use_extuni : bool;
    mutable ordering : Orderings.ordering;
    mutable max_local_time : int;
    mutable sos : bool;
    mutable use_extcnf_combined : bool;
    mutable expand_extuni : bool;
  }

(*LEO's main search state*)
type state = {
    mutable origproblem : (string, string*term) Hashtbl.t;
    mutable origproblem_filename : string;
    mutable origproblem_definitions : string;
    mutable origproblem_all_def_names : string;
    mutable signature : signature;
    mutable index : role termindex;
    mutable active : Set_of_clauses.t;
    mutable passive : Set_of_clauses.t;
    mutable active_debug : cl_clause list;
    mutable passive_debug : cl_clause list;
    mutable primsubst_waitlist : Set_of_clauses.t;
    mutable problem_axioms : cl_clause list;
    mutable problem_stack : cl_clause list;
    mutable free_var_count : int;
    mutable skolem_const_count : int;
    mutable clause_count : int;
    mutable loop_count : int;
    mutable clause_weight_func : cl_clause -> int;
    mutable empty_clauses : cl_clause list;
    mutable fo_clauses : (string * string) list;
    (*Used by new translation module, to avoid committing
      early to a particular typing of formulas*)
    mutable fo_clauses_new : (string * Af.af) list;
    (*count calls to external provers*)
    (*FIXME doesn't differentiate between provers*)
    mutable foatp_calls : int;
    mutable choice_functions : term list;
    (*The lambda abstractions the problem itself contains, by type, gathered
      once after the definitions are unfolded and before clause normalisation.
      A universal variable instantiated with one of them is an instance, so
      this can cost search and never a refutation; what it buys is the
      instantiation a problem hands you rather than one the prover has to
      invent.  See instantiate_max.*)
    mutable problem_abstractions : (hol_type * term) list;
    (*True only while the problem is first normalised.  The instantiation rule
      is for the quantifiers the problem is written with, once; left on it
      fires at every universal quantifier of a matching type that normalising
      ever produces, which on GoedelVariantHOML3/NegProps was ten thousand
      times and buried the proof.*)
    mutable instantiating : bool;
    (*How many quantifier positions may still be instantiated.  A budget and
      not a gate, because normalising is run to a fixpoint: every instance is
      itself normalised, offers the same quantifier again, and instantiates
      again.  Without a budget that loop fired ten thousand times on one
      problem.*)
    mutable instantiation_budget : int;
    mutable flags : flags;
  }

(*FIXME move inside "state" record? but then would
        need to make "state" value global*)
let current_success_status = ref Unknown
let state_at_last_status_change : state option ref = ref None

let get_current_success_status () = !current_success_status
let set_current_success_status st szs_st =
  current_success_status := szs_st;
  state_at_last_status_change := st

exception Termination of state option

let state_initialize =
  current_success_status := Unknown;
  let i = 10 in
    {
      origproblem = Hashtbl.create i;
      origproblem_filename = "";
      origproblem_definitions = "";
      origproblem_all_def_names = "";
      signature = new_signature ();
      index = new_index (new_termset ());
      active = Set_of_clauses.empty;
      passive = Set_of_clauses.empty;
      active_debug = [];
      passive_debug = [];
      primsubst_waitlist = Set_of_clauses.empty;
      problem_axioms = [];
      problem_stack = [];
      free_var_count = 0;
      skolem_const_count = 0;
      clause_count = 0;
      loop_count = 0;
      (* FIXME: not used yet -- should be used as
         compare function in clauseset *)
      clause_weight_func = cl_weight;
      empty_clauses = [];
      fo_clauses = [];
      fo_clauses_new = [];
      problem_abstractions = [];
      instantiating = false;
      instantiation_budget = 0;
      foatp_calls = 0;
      choice_functions = [];
      flags = {verbose = false;
               max_clause_count = -1;
               max_loop_count = -1;
               max_uni_depth = 6;
               write_protocol_files = false;
               write_fo_like_clauses = false;
               pretty_print_only = false;
               fo_translation = "fof_full";
               atp_calls_frequency = 5;
               atp_prover = "none";
               atp_timeout = 25;
               proof_output = 0;
               protocol_output = false;
               prim_subst = 3;
               unfold_defs_early = true;
               defs_as_rules = false;
               atp_max_clauses = 0;
               instantiate_max = 0;
               relevance_filter = 0;
               relevance_tolerance = -1;
               replace_leibnizEQ = true;
               replace_andrewsEQ = true;
               use_choice = true;
               use_extuni = true;
               max_local_time = 600;
               ordering = Orderings.None;
               sos = true;
               use_extcnf_combined = true;
               expand_extuni = false;
              }
    }


(*Synchronises the debug and non-debug active/passive
  sets of the state. Debug versions are legible during
  debugging*)
let indexedclauses_to_explicitlist clauseset =
  List.map (fun cl ->
              {cl with
                 cl_litarray =
                  Array.map
                    (fun l ->
                       {l with lit_term = Explicit (xterm2term l.lit_term)})
                    cl.cl_litarray;}) (Set_of_clauses.elements clauseset)

let state_reset (ls : state) =
  current_success_status := Unknown;
  reset_input_logic ();
  ls.origproblem <- Hashtbl.create 10;
  ls.origproblem_filename <- "";
  ls.origproblem_definitions <- "";
  ls.origproblem_all_def_names <- "";
  ls.signature <- new_signature ();
  ls.index <- new_index (new_termset ());
  ls.active <- Set_of_clauses.empty;
  ls.passive <- Set_of_clauses.empty;
  ls.active_debug <- [];
  ls.passive_debug <- [];
  ls.primsubst_waitlist <- Set_of_clauses.empty;
  ls.problem_axioms <- [];
  ls.problem_stack <- [];
  ls.free_var_count <- 0;
  ls.skolem_const_count <- 0;
  ls.clause_count <- 0;
  ls.loop_count <- 0;
  ls.clause_weight_func <- cl_weight;
  ls.empty_clauses <- [];
  ls.fo_clauses <- [];
  ls.fo_clauses_new <- [];
  ls.foatp_calls <- 0; (*FIXME should be reset?*)
  ls.choice_functions <- [];
  ()

let state_reset_only_essentials (ls : state) =
  current_success_status := Unknown;
  ls.origproblem <- Hashtbl.create 10;
  ls.signature <- new_signature ();
  ls.index <- new_index (new_termset ());
  ls.active <- Set_of_clauses.empty;
  ls.passive <- Set_of_clauses.empty;
  ls.active_debug <- [];
  ls.passive_debug <- [];
  ls.primsubst_waitlist <- Set_of_clauses.empty;
  ls.problem_axioms <- [];
  ls.problem_stack <- [];
  ls.free_var_count <- 0;
  ls.skolem_const_count <- 0;
  ls.clause_count <- 0;
  ls.loop_count <- 0;
  ls.clause_weight_func <- cl_weight;
  ls.empty_clauses <- [];
  ls.fo_clauses <- [];
  ls.fo_clauses_new <- [];
  ls.foatp_calls <- 0; (*FIXME should be reset?*)
  ls.choice_functions <- [];
  ()

let set_origproblem (ls : state)
    (h : (string, string * term) Hashtbl.t) =
  ls.origproblem <- h

let set_origproblem_filename (ls : state) (s : string) =
  ls.origproblem_filename <- s

let set_origproblem_definitions (ls : state) (s : string) =
  ls.origproblem_definitions <- s

let set_origproblem_all_def_names (ls : state) (s : string) =
  ls.origproblem_all_def_names <- s

let set_signature (ls : state) (sg : signature) =
  Termsystem.set_signature ls.signature;
  ls.signature <- sg

let set_active (ls : state) (cls : Set_of_clauses.t) =
  ls.active <- cls

let add_to_active (ls : state) (cl : cl_clause) =
  ls.active <- Set_of_clauses.add cl ls.active

let remove_from_active (ls : state) (cl : cl_clause) =
  ls.active <- Set_of_clauses.remove cl ls.active

let set_passive (ls : state) (cls : Set_of_clauses.t) =
  ls.passive <- cls

let set_primsubst_waitlist (ls : state) (cls : Set_of_clauses.t) =
  ls.primsubst_waitlist <- cls

let add_to_passive (ls : state) (cl : cl_clause) =
  ls.passive <- Set_of_clauses.add cl ls.passive

let add_to_primsubst_waitlist (ls : state) (cl : cl_clause) =
  ls.primsubst_waitlist <- Set_of_clauses.add cl ls.primsubst_waitlist

let remove_from_passive (ls : state) (cl : cl_clause) =
  ls.passive <- Set_of_clauses.remove cl ls.passive

let remove_from_primsubst_waitlist (ls : state) (cl : cl_clause) =
  ls.primsubst_waitlist <- Set_of_clauses.remove cl ls.primsubst_waitlist

let set_problem_axioms (ls : state) (prob : cl_clause list) =
  ls.problem_axioms <- prob

let set_problem_stack (ls : state) (prob : cl_clause list) =
  ls.problem_stack <- prob

let set_choice_functions (ls : state) (list: term list) =
  ls.choice_functions <- list;
  list

let rec show_list l = match l with 
       [a] -> a
     | a::b -> a^", "^(show_list b)
     | [] -> ""

let add_choice_functions (ls : state) (list: term list) =
  let rec help ls list =
    match list with
	[] -> ls.choice_functions
      | hd::tl -> 
	  if List.mem hd ls.choice_functions
	  then help ls tl 
	  else 
	    let _ = ls.choice_functions <- hd::ls.choice_functions in
              Util.sysoutf 0 (fun () -> ("\n *** Modified list of choice operators: "^(show_list (List.map Term.to_string ls.choice_functions))^" ***\n"));
	      help ls tl in
  let res = help ls list in
    res
	      
let set_index (ls : state) (tl : term list) =
  let ts = new_termset () in
  let idx = new_index ts
  in
    Termsystem.set_signature ls.signature;
    List.iter (fun t -> let id_t = create ts t in index_node id_t idx) tl;
    (*destructive insertion*)
    ls.index <- idx

let add_to_index (ls : state) (t : term) =
  let idx = ls.index in
  let ts = idx.termbase in
  let id_t = create ts t
  (*destructive insertion*)
  in index_node id_t idx

let set_free_var_count (ls : state) (i : int) =
  ls.free_var_count <- i;
  ls.free_var_count

let inc_free_var_count (ls : state) =
  ls.free_var_count <- ls.free_var_count + 1;
  ls.free_var_count

let set_skolem_const_count (ls : state) (i : int) =
  ls.skolem_const_count <- i;
  ls.skolem_const_count

let inc_skolem_const_count (ls : state) =
  ls.skolem_const_count <- ls.skolem_const_count + 1;
  ls.skolem_const_count

let set_clause_count (ls : state) (i : int) =
  ls.clause_count <- i;
  ls.clause_count

let inc_clause_count (ls : state) =
  ls.clause_count <- ls.clause_count + 1;
  ls.clause_count

let inc_loop_count (ls : state) =
  ls.loop_count <- ls.loop_count + 1;
  ls.loop_count

let set_loop_count (ls : state) (i : int) =
  ls.loop_count <- i;
  ls.loop_count

let set_clause_weight_func (ls : state) (func : cl_clause -> int) =
  ls.clause_weight_func <- func;
  func

let set_empty_clauses (ls : state) (cll : cl_clause list) =
  ls.empty_clauses <- cll;
  cll

let set_fo_clauses (ls : state) (cls : (string * string) list) =
  ls.fo_clauses <- cls

let set_flag_verbose  (ls : state) (flag : bool) =
  ls.flags.verbose <- flag;
  flag

let set_flag_sos (ls : state) (flag : bool) =
  ls.flags.sos <- flag;
  flag

let set_flag_max_clause_count (ls : state) (i : int) =
  ls.flags.max_clause_count <- i;
  i

let set_flag_max_loop_count (ls : state) (i : int) =
  ls.flags.max_loop_count <- i;
  i

let set_flag_max_uni_depth (ls : state) (i : int) =
  ls.flags.max_uni_depth <- i;
  i

let set_flag_write_protocol_files (ls : state) (flag : bool) =
  ls.flags.write_protocol_files <- flag;
  flag

let set_flag_write_fo_like_clauses (ls : state) (flag : bool) =
  ls.flags.write_fo_like_clauses <- flag;
  flag

let set_flag_pretty_print_only (ls : state) (flag : bool) =
  ls.flags.pretty_print_only <- flag;
  flag

let set_flag_fo_translation (ls : state) (str : string) =
  ls.flags.fo_translation <- str;
  str

let set_flag_atp_calls_frequency (ls : state) (i : int) =
  ls.flags.atp_calls_frequency <- i;
  i

let set_flag_atp_prover (ls : state) (str : string) =
  ls.flags.atp_prover <- str;
  str

let set_flag_atp_timeout (ls : state) (i : int) =
  ls.flags.atp_timeout <- i;
  i

let set_flag_proof_output (ls : state) (level : int) =
  ls.flags.proof_output <- level;
  level

let set_flag_protocol_output (ls : state) (value : bool) =
  ls.flags.protocol_output <- value;
  value

let set_flag_prim_subst (ls : state) (flag : int) =
  ls.flags.prim_subst <- flag;
  flag

let set_flag_defs_as_rules (ls : state) (flag : bool) =
  ls.flags.defs_as_rules <- flag;
  flag

let set_flag_atp_max_clauses (ls : state) (flag : int) =
  ls.flags.atp_max_clauses <- flag;
  flag

let set_flag_instantiate_max (ls : state) (flag : int) =
  ls.flags.instantiate_max <- flag;
  flag

let set_flag_unfold_defs_early (ls : state) (flag : bool) =
  ls.flags.unfold_defs_early <- flag;
  flag

let set_flag_relevance_filter (ls : state) (i : int) =
  ls.flags.relevance_filter <- i;
  i

let set_flag_relevance_tolerance (ls : state) (i : int) =
  ls.flags.relevance_tolerance <- i;
  ls.flags.relevance_tolerance

let set_flag_replace_leibnizEQ (ls : state) (flag : bool) =
  ls.flags.replace_leibnizEQ <- flag;
  flag

let set_flag_replace_andrewsEQ (ls : state) (flag : bool) =
  ls.flags.replace_andrewsEQ <- flag;
  flag

let set_flag_use_choice (ls : state) (flag : bool) =
  ls.flags.use_choice <- flag;
  flag

let set_flag_use_extuni (ls : state) (flag : bool) =
  ls.flags.use_extuni <- flag;
  flag

let set_flag_use_extcnf_combined (ls : state) (flag : bool) =
  ls.flags.use_extcnf_combined <- flag;
  flag

let set_flag_expand_extuni (ls : state) (flag : bool) =
  ls.flags.expand_extuni <- flag;
  flag

let set_flag_max_local_time (ls : state) (i : int) =
  ls.flags.max_local_time <- i;
  i

let set_flag_termorder (ls : state) (order : Orderings.ordering) =
  ls.flags.ordering <- order;
  order

let get_flag_termorder (ls : state) =
  ls.flags.ordering


(** Info provided to the outside **)

(*Provide summary of prover state. This is used to
  inform the user on exit, and could be used in
  intermediate stages*)
let summary_stats_string st =
  "(rf:" ^ string_of_int st.flags.relevance_filter ^
    ",axioms:" ^ string_of_int (List.length st.problem_axioms) ^
    ",ps:" ^ string_of_int st.flags.prim_subst ^
    (* ",sos:" ^ string_of_bool st.flags.sos ^ *)
    ",u:" ^ string_of_int st.flags.max_uni_depth ^
    ",ude:" ^ string_of_bool st.flags.unfold_defs_early ^
    ",rLeibEQ:" ^ string_of_bool st.flags.replace_leibnizEQ ^
    ",rAndEQ:" ^ string_of_bool st.flags.replace_andrewsEQ ^
    ",use_choice:" ^ string_of_bool st.flags.use_choice ^
    ",use_extuni:" ^ string_of_bool st.flags.use_extuni ^
    ",use_extcnf_combined:" ^ string_of_bool st.flags.use_extcnf_combined ^
    ",expand_extuni:" ^ string_of_bool st.flags.expand_extuni ^
    ",foatp:" ^ st.flags.atp_prover ^
    ",atp_timeout:" ^ string_of_int st.flags.atp_timeout ^
    ",atp_calls_frequency:" ^ string_of_int st.flags.atp_calls_frequency ^
    ",ordering:" ^ Orderings.ordering_to_string st.flags.ordering ^
    ",proof_output:" ^ string_of_int st.flags.proof_output ^
    ",protocol_output:" ^ string_of_bool st.flags.protocol_output ^
    ",clause_count:" ^ string_of_int st.clause_count ^
    ",loop_count:" ^ string_of_int st.loop_count ^
    ",foatp_calls:" ^ string_of_int st.foatp_calls ^
    ",translation:" ^ st.flags.fo_translation ^
    ")"

(*The SZS status should always be shown prior to termination*)
let szs_result maybe_st =
  let prob_file =
    (*could also be obtained from "st", but "st" is not always available*)
    if !current_problem_file = "" then
      ""
    else
      "for " ^ !current_problem_file in
  let extra_info =
    match maybe_st with
        None ->
          begin
            match !state_at_last_status_change with
                None -> ""
              | Some st -> ": " ^ summary_stats_string st
          end
      | Some st -> ": " ^ summary_stats_string st
  in
    "% SZS status " ^ szs_status_string !current_success_status ^
      " " ^ prob_file ^ " " ^ extra_info ^
      (if !question_answers <> [] && !current_success_status = Theorem then
         "\n% SZS answers Tuple [[" ^ String.concat ", " !question_answers ^ "]]"
       else "")

let szs_exitcode () =
  szs_status_exitcode !current_success_status

(*This should always be one less than the current loop count*)
let lastloop_no = ref 0

(*This indicates whether the main loop's main body was executed during the
  last loop. This is not the case if e.g. the lightest clause was subsumed.*)
let lastloop_ran = ref false

(*Prints prover state (focussing on active and passive clause sets) in DOT format.
  lightest : the lightest clause in the passive set.
  lightest' : like lightest, but with free variables renamed.
  st : the prover's state record.
  ignored_clauses : clauses which are derived from, but not included (e.g. due to subsumption)
    in the passive/active sets.
*)
let print_actpas_sets lightest lightest' ignored_clauses st =
  (*FIXME beware use of "compare" below*)
  let loopK = "Loop" in
  let lastloop_name = loopK ^ string_of_int !lastloop_no in
  let curloop_name = loopK ^ string_of_int st.loop_count in
    Util.sysoutf 0 (fun () -> ("\"" ^ curloop_name ^ "\"[\n"));
    Util.sysout 0 ("  shape = record\n");
    Util.sysoutf 0 (fun () -> ("  label = \"<head>" ^ loopK ^ " " ^ string_of_int st.loop_count ^ " | {" ^
      String.concat " | "
        (List.map (fun cl ->
                     "<f" ^ string_of_int cl.cl_number ^ "> " ^ string_of_int cl.cl_number)
           (List.sort Stdlib.compare (Set_of_clauses.elements st.passive))) ^
      "} | {"));

    Util.sysoutf 0 (fun () -> (String.concat " | "
        (List.map (fun cl ->
                     "<f" ^ string_of_int cl.cl_number ^ "> " ^ string_of_int cl.cl_number)
           (List.sort Stdlib.compare (Set_of_clauses.elements st.active))) ^
      "} | {"));

    let ignored_clauses' =
      (*ignored_clauses should be disjoint from active & passive sets,
        but i noticed that this isn't always the case.*)
      Set_of_clauses.filter
        (fun cl -> not (Set_of_clauses.mem cl st.active))
        ignored_clauses
    in
    (*FIXME possible improvement:
      if !lastloop_no = 0 then print all the clauses in the protocol so far,
      to include the clauses generated during preprocessing.*)
    Util.sysoutf 0 (fun () -> (String.concat " | "
        (List.map (fun cl ->
                     "<f" ^ string_of_int cl.cl_number ^ "> " ^ string_of_int cl.cl_number)
           (List.sort Stdlib.compare (Set_of_clauses.elements ignored_clauses'))) ^
      "}\"\n];\n"));

    if !lastloop_no > 0 then
      if !lastloop_ran then
        Util.sysoutf 0 (fun () -> (lastloop_name ^ ":f" ^ string_of_int lightest.cl_number ^ " -> " ^
                         curloop_name ^ ":f" ^ string_of_int lightest'.cl_number ^ ";\n"))
      else
        Util.sysoutf 0 (fun () -> (lastloop_name ^ ":f" ^ string_of_int lightest.cl_number ^ " -> " ^
                         curloop_name ^ ":head;\n"));

    lastloop_no := st.loop_count;
