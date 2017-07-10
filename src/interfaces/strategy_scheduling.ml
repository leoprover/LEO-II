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
    Util.sysout 1 ("\nLEO-II: " ^ cmd);
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
let compute_strategies global_conf filename : string list list =
  let body =
    if global_conf.analyze
    then [["read-problem-file " ^ filename;
	         "analyze "]]
		else
      let _ = Cmdline.execute_command ("read-problem-file " ^ filename) in
      let (no_of_axioms,length_of_definitions,contains_choice_funs) = 
        analyze_problem !leo_state in
        Util.sysout 0 ("\n No.of.Axioms: " ^ string_of_int no_of_axioms ^ "\n");
        Util.sysout 0 ("\n Length.of.Defs: " ^ string_of_int length_of_definitions ^ "\n");
        Util.sysout 0 ("\n Contains.Choice.Funs: " ^ string_of_bool contains_choice_funs^ "\n");
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
	            [["flag-unfold-defs-early"; (* sets it to true *)
		            "read-problem-file " ^ filename;
	              "prove-with-fo-atp " ^ global_conf.foatp]] @
	              [["flag-unfold-defs-early"; (* sets it to false *)
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
       
       
