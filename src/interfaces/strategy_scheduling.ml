(* Leo-II's strategy schedules

TODO:
* Could give each strategy a "MODE" name,
   as in TPS and Satallax
* Could also include constraints on how many
   times an ATP should be called during that
   strategy.
*)

open Cmdline
open Interactive
open Automation
open State

exception STRATEGY of string

(*Executes list of commands, until we execute
  a command that changes current_success_status
  from Unknown*)
let rec execute_commands cmds =
  let execute cmd =
    Util.sysoutf 1 (fun () -> ("\nLEO-II: " ^ cmd));
    Cmdline.execute_command cmd in
  match cmds with
      [] -> raise (STRATEGY "Empty strategy")
    | [s] -> execute s
    | s :: ss ->
        assert (get_current_success_status () = Unknown);
        ignore(execute s);
        if get_current_success_status () = Unknown then
          execute_commands ss
        else true

(*a strategy is a list of commands. this function produces
  a list of strategies based on the problem's features*)
(* What a portfolio measurement says about the strategies below, so that the
   next person need not repeat it.

   Every setting LEO-II can be given was run, one at a time with the full time
   limit, over the 126 of the 294 higher-order problems of Benzmueller and
   Scott's ontological-argument dataset that the plain configuration does not
   solve.  Eighteen settings, ten seconds each.  What they contribute, counted
   as problems the plain configuration does not get:

     relevance filter 1                20      prim-subst 0              6
     clause selection by weight         6      no extensional unif.      5
     unfold-defs late                   2      max-uni-depth 3           2
     max-uni-depth 10                   2      atp-timeout 5             1
     no Andrews-EQ replacement          1      the other eight           0

   Three things follow.

   The settings this function reaches for are among the ones that contribute
   nothing: relevance filter 2 and prim-subst 2 and 3 solve none of the 126.
   Filtering at level 2 is weaker than at level 1, not stronger, because the
   tolerance falls with each round, so a higher level admits more in its first
   round.  Raising prim-subst never paid; turning it off did.

   The individual contributions sum to 46 but cover only 29 distinct problems,
   and 97 of the 126 are out of reach of every setting.  No arrangement of
   these flags will find them.

   And a schedule built from those numbers -- plain, then filter 1, then
   prim-subst 0 -- was measured and gains nothing: 167 against 168 at a ten
   second limit, 179 against 178 at sixty.  The reason is a flaw in the
   arithmetic, not in the settings: the portfolio measured each setting with
   the whole budget, while a schedule gives it a share, and what the added
   strategies find the shortened first slice loses.  A portfolio meant to
   predict a schedule must measure each setting at the slice length it will
   actually get.

   The strategies below were therefore left as they were -- until the
   first-order calls were spaced out (2.0), which made the filtered strategy
   fast enough for a short slice.  Measured 2026-09-22 on the 294, ten seconds,
   one core, default 205: relevance filter 1 in the second of two equal slices
   213 (gains the five Ax2a_prime, six UniqueEss3, two GNonempty; loses five
   PosOfGod, Th4, two Pos, which need more than five seconds unfiltered); the
   same in the first slice 207; the filter first with a quarter of the budget
   and the rest to the unfiltered search 217, losing two; the filter last
   with a quarter 211.  The branch for problems with long definitions -- the
   one the ontological-argument problems take -- now opens with that short
   filtered slice; the slice lengths are set in leo.ml.  The filtered proofs
   take 0.1 to 1.1 seconds; what the filter does not find fast it does not
   find at all, and the unused time falls to the last slice. *)

let compute_strategies global_conf filename : string list list =
  let body =
    if global_conf.analyze
    then [["read-problem-file " ^ filename;
	         "analyze "]]
		else
      let _ = Cmdline.execute_command ("read-problem-file " ^ filename) in
      let (no_of_axioms,length_of_definitions,contains_choice_funs) = 
        analyze_problem !leo_state in
        Util.sysoutf 0 (fun () -> ("\n No.of.Axioms: " ^ string_of_int no_of_axioms ^ "\n"));
        Util.sysoutf 0 (fun () -> ("\n Length.of.Defs: " ^ string_of_int length_of_definitions ^ "\n"));
        Util.sysoutf 0 (fun () -> ("\n Contains.Choice.Funs: " ^ string_of_bool contains_choice_funs^ "\n"));
        match (global_conf.time_slices,global_conf.global_timeout,no_of_axioms,length_of_definitions,contains_choice_funs) with
	          (sl,_,_,_,_) when sl = 1 -> 
	            [["read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]] 
	        | (sl,tmo,ax,_,_) when tmo < 6 && ax < 100-> 
	            [["flag-max-uni-depth 3";
	              "read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]]
	        | (sl,tmo,_,_,_) when tmo < 6 -> 
	            [["flag-relevance-filter 2";
		            "flag-max-uni-depth 3";
	              "read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]]
	        | (_,_,ax,_,false) when ax > 100 -> 
              [["flag-relevance-filter 2";
		            "flag-prim-subst 3";
		            "flag-max-uni-depth 5";
		            "read-problem-file " ^ filename;
		            "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-relevance-filter 0";
		              "flag-prim-subst 0";
		              "flag-max-uni-depth 1";
		              "flag-use-extuni"; (* sets it to false *)
		              "flag-unfold-defs-early false" (* sets it to false *);
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-relevance-filter 2";
		              "flag-replace-andrewsEQ"; (* sets it to false *)
		              "flag-replace-leibnizEQ"; (* sets it to false *)
		              "flag-unfold-defs-early"; (* sets it to true *)
                  "flag-use-extuni"; (* sets it to true *)
		              "flag-prim-subst 0";
		              "flag-max-uni-depth 1";
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
                [["flag-relevance-filter -1";
                  "flag-replace-andrewsEQ"; (* sets it to true *)
		              "flag-replace-leibnizEQ"; (* sets it to true *)
		              "flag-prim-subst 0";
		              "flag-max-uni-depth 1";
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]]
	        | (_,_,ax,defs,false) when ax <= 100 && defs > 1000 -> 
	            [["flag-relevance-filter 1";
		            "read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-relevance-filter 0";
		              "flag-max-uni-depth 3";
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-prim-subst 0";
		              "flag-max-uni-depth 0";
		              "flag-use-extuni"; (* sets it to false *)
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-replace-andrewsEQ"; (* sets it to false *)
		              "flag-replace-leibnizEQ"; (* sets it to false *)
		              "flag-max-uni-depth 1";
		              "flag-prim-subst 0";
		              "flag-use-choice";  (* sets it to false *)
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]]
	        | (_,_,_,_,false) ->  
	            [["flag-max-uni-depth 6";
	              "read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-unfold-defs-early"; (* sets it to false *)
		              "flag-prim-subst 2";
		              "flag-max-uni-depth 1";
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-prim-subst 3";
		              "flag-max-uni-depth 8";
		              "flag-use-extuni";
		              "flag-unfold-defs-early"; (* sets it to true *)
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-relevance-filter 2";
		              "flag-replace-andrewsEQ"; (* sets it to false *)
		              "flag-replace-leibnizEQ"; (* sets it to false *)
		              "flag-max-uni-depth 3";
		              "flag-prim-subst 1";
		              "flag-use-choice";  (* sets it to false *)
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]]
	        | (_,_,_,_,true) ->
	            [["flag-max-uni-depth 1";
                "flag-unfold-defs-early"; (* sets it to false *)
	              "read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-unfold-defs-early"; (* sets it to true *)
		              "flag-prim-subst 0";
		              "flag-max-uni-depth 1";
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-prim-subst 3";
		              "flag-max-uni-depth 8";
		              "flag-use-extuni";
		              "flag-unfold-defs-early"; (* sets it to true *)
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-relevance-filter 2";
		              "flag-replace-andrewsEQ"; (* sets it to false *)
		              "flag-replace-leibnizEQ"; (* sets it to false *)
		              "flag-max-uni-depth 3";
		              "flag-prim-subst 1";
		              "flag-use-choice";  (* sets it to false *)
		              "read-problem-file " ^ filename;
		              "prove-with-fo-atp " ^ global_conf.foatp]]
  in body
       
       
