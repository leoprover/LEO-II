open List
open Cmdline
open Interactive
open Automation
open State

IFDEF DEBUG THEN
  Printexc.record_backtrace true;
  Printexc.register_printer Translation.exc_printers;
END

Sys.catch_break true;;

IFDEF REV THEN
let rev = "(r" ^ string_of_int REV ^ ")"
ELSE
let rev = ""
END

let version () =
  print_endline ("LEO-II version v1.7 " ^ rev ^ " \
  (compiled on " ^ Sys.os_type ^ " with OCaml-" ^ Sys.ocaml_version ^ ")");
  if State.state_initialize.flags.verbose then Automation.atp_versions ()

type arg =
  | FILENAME of string (*name of file to process*)
  (*the rest of the arguments are described in "help ()" below*)
  | ANALYZE
  | ATP of string
  | ATPRC of string
  | ATPTIMEOUT of int
  | DEBUG of int
  | DIR of string
  | EXPAND_EXTUNI
  | FOATP of string
  | HELP
  | INTERACTIVE
  | NOSLICES
  | MAXUNIDEPTH of int (*FIXME unidepth*)
  | PRETTYPRINTONLY (*FIXME prettyPrintOrig*)
  | PRIMSUBST of int
  | PROOFOUTPUT of int
  | PROTOCOL_OUTPUT
  | RELEVANCEFILTER of int
  | NOTREPLACELEIBNIZEQ
  | NOTREPLACEANDREWSEQ
  | NOTUSECHOICE
  | NOTUSEEXTUNI
  | NOTUSE_EXTCNFCOMBINED
  | SCRIPTMODE
  | SOS
  | TIMEOUT of int
  | TMPPATH of string (*FIXME tmp*)
  | TRANSLATION of string
  | UNFOLDDEFSEARLY
  | UNFOLDDEFSLATE
  | VERBOSE
  | VERSION
  | ORDERING of string
  | WRITEFOCLAUSES

let help () = print_string ("\
    Usage: leo [OPTIONS] [FILE]\n\
    Options:\n \
     --analyze, -a              Compute and return features of the input problem for 
                                application in machine learning (used e.g. by MALES)
     --atp ATP=EXEC             Set the exec file for external prover ATP to EXEC\n \
                                (overrides the .leoatprc file, option can be used repeatedly)\n \
     --atprc FILE               Set ATP config file\n \
     --atptimeout N, -at N      Set the ATPtimeout (calls to E) to N seconds\n \
                                Default: 30s sec\n \
     --debug N, -D N            Set debug level to N\n \
                                (0 = no output, 1 = minimal output, 2 = full output)\n \
                                Default: 0\n \
     --dir DIR, -d DIR          Run on all files in DIR\n \
     --expand_extuni            Provide detailed unification inferences. \n \
     --foatp PROVER, -f PROVER  Select PROVER as first-order prover\n\tCurrently supported: " ^
                              String.concat ", " Automation.supported_atps ^ "\n\tDefault: " ^ global_conf.foatp ^ "\n \
     --help, -h                 Display this help screen and exit\n \
     --interactive, -i          Start interactive mode\n \
                                Default is non-interactive\n \
     --noslices -ns             Deactivates automatic time slicing; please use after the -t option e.g. as in leo -t 20 -ns file.p\n \
     --prettyPrintOrig, -ppo    Write pretty print of expanded original problem to a file (in tmp)\n \
     --primsubst N, -ps N       Set the prim subst level to N \n \
                                Default: 3\n \
     --proofoutput N, -po N     Print proof object \n \
                                N=0 (default): no proof output  \n \
                                N=1: Print proof object without detailed information on the fo-atp contribution \n \
                                N=2: Print proof object with detailed information on the fo-atp contribution \n \
     --protocoloutput           Print full proof protocol. \n \
     --relevancefilter N, -rf N Set the relevance filter to N\n \
                                Default: 0\n \
     --notReplLeibnizEQ, -nrleq Do not automatically replace Leibniz EQ literals in clauses \n \
     --notReplAndrewsEQ, -nraeq Do not automatically replace Andrews EQ literals in clauses \n \
     --notUseChoice,     -nuc   Do not use the choice rule \n \
     --notUseExtuni,     -nue   Do not use extensional unification \n \
     --notUseExtCnfCmbd, -nux   Do not use the extcnf_combined rule \n \
     --order ORDERING           Use ORDERING\n\tAvailable options: " ^
                                String.concat ", " (List.map Orderings.ordering_to_string Orderings.available_orderings) ^ "\n \
     --scriptmode, -s           Start script mode\n \
     --sos, -S                  (this flag is currently deactivated, don't use)\n \
     --timeout N, -t N          Enforce timeout after N seconds\n \
                                (0 = no timeout)\n \
                                Default: 600 sec\n \
     --tmp PATH, -tmp PATH      Set path for temporary files\n \
     --translation TRANSLATION  Use TRANSLATION into FOL\n\tAvailable translations: " ^
                              String.concat ", " (List.map Translation_general.print_translation Translation_general.fo_translations) ^ "\n \
     --unfolddefsearly, -ude    Prefer early unfolding of definitions \n \
     --unfolddefslate, -udl     Prefer late unfolding of definitions \n \
     --unidepth N, -u N         Set the maximal (pre-)unification depth to N\n \
                                Default: 5\n \
     --verbose, -V              Run in verbose mode\n \
     --version, -v              Display version information and exit\n \
     --writeFOclauses, -w       Write the first-order translations to a file (after termination)\n \
     \n")

let error msg =
  prerr_endline ("LEO-II: " ^ msg);
  prerr_endline ("Type \"" ^ Array.get Sys.argv 0 ^ " --help\" for argument info.");
  exit 255

(* try to read an integer from the command line arguments *)
let get_cl_int opt = function
  | [] -> error ("Option " ^ opt ^ " needs an argument.")
  | x :: xs ->
      try int_of_string x
      with _ -> error ("Option '" ^ opt ^ "' needs an argument.")

(* try to read a string from the command line arguments *)
let get_cl_string opt = function
  | [] -> error ("Option " ^ opt ^ " needs an argument.")
  | x :: _ -> x

(* parse command line arguments, return arg list. the arg list is accummulated
in "ps"*)
let rec parse_cl cs ps =
  match cs with
    | "-a" :: xs
    | "--analyze" :: xs ->
        parse_cl xs (ANALYZE :: ps)
    | "--atp" :: xs ->
        parse_cl (tl xs) (ATP (get_cl_string (hd cs) xs) :: ps)
    | "--atprc" :: xs ->
        parse_cl (tl xs) (ATPRC (get_cl_string (hd cs) xs) :: ps)
    | "-at" :: xs
    | "--atptimeout" :: xs ->
        parse_cl (tl xs) (ATPTIMEOUT (get_cl_int (hd cs) xs) :: ps)
    | "-D" :: xs
    | "--debug" :: xs ->
        parse_cl (tl xs) (DEBUG (get_cl_int (hd cs) xs) :: ps)
    | "-d" :: xs
    | "--dir" :: xs ->
        parse_cl (tl xs) (DIR (get_cl_string (hd cs) xs) :: ps)
    | "--expand_extuni" :: xs ->
        parse_cl xs (EXPAND_EXTUNI :: ps)
    | "-f" :: xs
    | "--foatp" :: xs ->
        parse_cl (tl xs) (FOATP (String.lowercase (get_cl_string (hd cs) xs)) :: ps)
    | "-h" :: xs
    | "--help" :: xs ->
        parse_cl xs (HELP :: ps)
    | "-i" :: xs
    | "--interactive" :: xs ->
        parse_cl xs (INTERACTIVE :: ps)
    | "-ns" :: xs
    | "--noslices" :: xs ->
        parse_cl xs (NOSLICES :: ps)
    | "-ppo" :: xs
    | "--prettyPrintOnly" :: xs ->
        parse_cl xs (PRETTYPRINTONLY :: ps)
    | "-ps" :: xs
    | "--primsubst" :: xs ->
        parse_cl  (tl xs) (PRIMSUBST (get_cl_int (hd cs) xs) :: ps)
    | "-po" :: xs
    | "--proofoutput" :: xs ->
        parse_cl (tl xs) (PROOFOUTPUT (get_cl_int (hd cs) xs) :: ps)
    | "--protocoloutput" :: xs ->
        parse_cl xs (PROTOCOL_OUTPUT :: ps)
    | "-rf" :: xs
    | "--relevancefilter" :: xs ->
        parse_cl (tl xs) (RELEVANCEFILTER (get_cl_int (hd cs) xs) :: ps)
    | "-nrleq" :: xs
    | "--notReplLeibnizEQ" :: xs ->
        parse_cl xs (NOTREPLACELEIBNIZEQ :: ps)
    | "-nraeq" :: xs
    | "--notReplAndrewsEQ" :: xs ->
        parse_cl xs (NOTREPLACEANDREWSEQ :: ps)
    | "-nuc" :: xs
    | "--notUseChoice" :: xs ->
        parse_cl xs (NOTUSECHOICE :: ps)
    | "-nue" :: xs
    | "--notUseExtuni" :: xs ->
        parse_cl xs (NOTUSEEXTUNI :: ps)
    | "-nux" :: xs
    | "--notUseExtCnfCmbd" :: xs ->
        parse_cl xs (NOTUSE_EXTCNFCOMBINED :: ps)
    | "-s" :: xs
    | "--scriptmode" :: xs ->
        parse_cl xs (SCRIPTMODE :: ps)
    | "-S" :: xs
    | "--sos" :: xs ->
        parse_cl xs (SOS :: ps)
    | "-t" :: xs
    | "--timeout" :: xs ->
        parse_cl (tl xs) (TIMEOUT (get_cl_int (hd cs) xs) :: ps)
    | "-tmp" :: xs
    | "--tmp" :: xs ->
        parse_cl (tl xs) (TMPPATH (get_cl_string (hd cs) xs) :: ps)
    | "--translation" :: xs ->
        parse_cl (tl xs) (TRANSLATION (get_cl_string (hd cs) xs) :: ps)
    | "-ude" :: xs
    | "--unfolddefsearly" :: xs ->
        parse_cl xs (UNFOLDDEFSEARLY :: ps)
    | "-udl" :: xs
    | "--unfolddefslate" :: xs ->
        parse_cl xs (UNFOLDDEFSLATE :: ps)
    | "-u" :: xs
    | "--unidepth" :: xs ->
        parse_cl (tl xs) (MAXUNIDEPTH (get_cl_int (hd cs) xs) :: ps)
    | "-V" :: xs
    | "--verbose" :: xs ->
        parse_cl xs (VERBOSE :: ps)
    | "-v" :: xs
    | "--version" :: xs ->
        parse_cl xs (VERSION :: ps)
    | "--order" :: xs ->
        parse_cl (tl xs) (ORDERING (get_cl_string (hd cs) xs) :: ps)
    | "-w" :: xs
    | "--writeFOclauses" :: xs ->
        parse_cl xs (WRITEFOCLAUSES :: ps)
    | x :: xs ->
          if String.get x 0 = '-'
          then error ("Unknown command line argument \'" ^ x ^ "\'.")
          else
            (*the argument must be a filename, so attempt to parse it.*)
            parse_cl xs (FILENAME x :: ps)
    | [] -> ps (*return the arglist*)

let cleanup () =
  Interactive.kill_children ();
  Util.delete_all_tmpfiles ()

(*FIXME move to State, or delete -- left here temporarily for testing*)
IFDEF DEBUG THEN
let sched_num = ref 0
let sched_inc () =
  let next = 1 + !sched_num
  in
    sched_num := next;
    next
END

(*This function oversees the running schedules, and controlled is returned to
  this function when a schedule's timeout expires. It consumes the schedules
  from a queue and runs them for the scheduled duration. The queue is created
  at the start of the Leo2 process.*)
let run_schedules () =
  (*assumes schedule queue isn't empty*)
  let run_next_schedule () =
    let schedule = Queue.take global_conf.schedules in
    (*if this is the last schedule and we have unused time from earlier slices,
      use it now (or, if we've used up too much time previously, decrement from
      this strategy's time)*)
    let duration =
      (*in any case, correct for overshot*)
      if Queue.is_empty global_conf.schedules then
        float global_conf.global_timeout -. !State.problem_cumulative_time -. !State.problem_overshot
      else
        schedule.duration -.
          (!State.problem_overshot /. float (Queue.length global_conf.schedules)) in
    (*Timeout for the ATP*)
    let atptmo =
      (*FIXME constants can be made parameters*)
      min 25
        (max 3
           (int_of_float (duration /. float State.atp_subslices)))
    in
      IFDEF DEBUG THEN
        Util.sysout 2 ("Schedule " ^ string_of_int (sched_inc ()) ^
                         " (total of " ^ string_of_float duration ^ "s" ^
                         ", E gets slices of maximum " ^ string_of_int atptmo ^ ")\n")
      END;

      State.set_current_success_status None Unknown;
      begin
        match State.global_conf.atp_timeout_forced with
            None -> ignore(State.set_flag_atp_timeout State.state_initialize atptmo)
          | Some forced_timeout ->
              if forced_timeout > atptmo then
                prerr_endline ("WARNING: forcing ATP timeout of " ^ string_of_int forced_timeout ^ "s" ^
                                 " but strategy would have assigned " ^ string_of_int atptmo ^ "s");
              ignore(State.set_flag_atp_timeout State.state_initialize forced_timeout)
      end;
      State.current_schedule := {schedule with duration = duration};
      State.child_time := 0.0;
      State.problem_overshot := 0.0;
      State.schedule_start := Unix.gettimeofday () +. duration;
      Strategy_scheduling.execute_commands schedule.strategy in
  let solved = ref false
  in
    (*having completed the schedule, check if there's a next schedule to run*)
    while (not (Queue.is_empty global_conf.schedules) && not !solved)
    do
      let start_time = Unix.gettimeofday () in
      try
        solved := run_next_schedule ()
      with State.STRATEGY_TERMINATED -> ();

      State.problem_cumulative_time := !State.problem_cumulative_time +.
        !State.current_schedule.duration;
      State.problem_overshot := !State.problem_overshot +.
        (Unix.gettimeofday () -. start_time) -. !State.current_schedule.duration;
    done;

    if not !solved &&
      !State.problem_cumulative_time > float global_conf.global_timeout then
      set_current_success_status None Timeout
    (*otherwise if we haven't solved by haven't exceeded timeout, leave status as is*)

(*FIXME move to some library module*)
(*Take up to n items from the prefix of l;
  doesn't complain if there are fewer than n elements in l*)
let take_upto n l =
  let rec take_upto' n revacc l =
    if n = 0 then revacc
    else
      match l with
          [] -> revacc
        | (x :: xs) -> take_upto' (n - 1) (x :: revacc) xs
  in List.rev (take_upto' n [] l)

let execute_conf () =
  (*FIXME hack -- set hook in Orderings*)
  Orderings.set_ord (State.get_flag_termorder State.state_initialize);
  if global_conf.interactive
  then comint ()
  else
    begin
      ignore(Interactive.initialize ());
      if global_conf.dir <> ""
      then
        let cmd = "prove-directory-with-fo-atp " ^ global_conf.dir ^ " " ^
          global_conf.foatp
        in
          print_endline ("\nLEO-II: " ^ cmd);
          ignore (Cmdline.execute_command cmd)
      else
        (*FIXME check behaviour when run on multiple problem files*)
        if global_conf.problemfiles <> [] then
          let compute_schedules_for_prob probfilename =
            (*FIXME currently each schedule is given an equal slice of time*)
            let timeslice = max 1 (global_conf.global_timeout / global_conf.time_slices) in
            (*compute schedules, limited by time_slices value*)
            let schedules =
              take_upto global_conf.time_slices
                (Strategy_scheduling.compute_strategies global_conf probfilename)
            in
              Queue.clear global_conf.schedules;
              IFDEF DEBUG THEN
                Util.sysout 2 ("Duration of slices: " ^ string_of_int timeslice)
              END;
              (*enqueue schedules*)
              List.iter
                (fun strat ->
                   let sched : schedule =
                     {duration = float_of_int timeslice;
                      strategy = strat}
                   in
                     Queue.add sched global_conf.schedules)
                schedules;

              (*start*)
              State.problem_cumulative_time := 0.;
              Translation.reset_prev_fo_clauses_cache ();
              ignore(run_schedules ());
              sys_time_offset := !sys_time_offset +. !State.problem_cumulative_time;

              Util.sysout 0 (State.szs_result None(*FIXME state info not available?*)
                                          ^ "\n")
          in
            begin
              sys_time_offset := Sys.time ();
              List.iter compute_schedules_for_prob global_conf.problemfiles
          end
        else error "No problem file given."
    end

(* process the argument list, build the configuration record
 * and finally call execute_conf *)
let rec process args = match args with
  | FILENAME s :: args ->
      global_conf.problemfiles <- s :: global_conf.problemfiles;
      process args
  | ATP s :: args ->
      let eqpos = String.index s '=' in
      let len = String.length s in
      let atp = String.sub s 0 eqpos in
      let executable = String.sub s (eqpos + 1) (len - eqpos - 1) in
      (* print_string ("ATP: "^atp^", exec: "^executable^"\n"); *)
      if Sys.file_exists executable 
      then
	( Automation.atp_cmds := (atp, executable) :: !Automation.atp_cmds;
	  Automation.atp_configured := true;
	  Util.sysout 1 ("  Configured: " ^ atp ^ " = " ^ executable ^ "\n");
	);
	process args
  | ANALYZE :: args ->
      global_conf.analyze <- true;
      process args
  | ATPRC s :: args ->
      Automation.atp_config_file := s;
      process args
  | ATPTIMEOUT n :: args ->
      global_conf.atp_timeout_forced <- Some n;
      ignore(State.set_flag_atp_timeout State.state_initialize (max 5 n));
      process args
  | DEBUG n :: args ->
      global_conf.debug <- n;
      Util.debuglevel := n;
      process args
  | DIR s :: args ->
      global_conf.dir <- s;
      process args
  | EXPAND_EXTUNI :: args ->
      ignore(State.set_flag_expand_extuni State.state_initialize true);
      process args
  | FOATP s :: args ->
      global_conf.foatp <- s;
      process args
  | HELP :: args ->
      help ()
  | INTERACTIVE :: args ->
      global_conf.interactive <- true;
      Cmdline.interactive := true;
      Util.debuglevel := 1;
      Cmdline.save_tcio ();
      process args
  | NOSLICES :: args ->
      global_conf.time_slices <- 1;
      process args
  | MAXUNIDEPTH n :: args ->
      ignore(State.set_flag_max_uni_depth State.state_initialize (max 1 n));
      process args
  | PRETTYPRINTONLY :: args ->
      ignore(State.set_flag_pretty_print_only State.state_initialize true);
      process args
  | PRIMSUBST n :: args ->
      ignore(State.set_flag_prim_subst State.state_initialize n);
      process args
  | PROOFOUTPUT n :: args ->
      ignore(State.set_flag_proof_output State.state_initialize n);
      process args
  | PROTOCOL_OUTPUT :: args ->
      ignore(State.set_flag_protocol_output State.state_initialize true);
      process args
  | RELEVANCEFILTER n :: args ->
      ignore(State.set_flag_relevance_filter State.state_initialize (max 0 n));
      process args
  | NOTREPLACELEIBNIZEQ :: args ->
      ignore(State.set_flag_replace_leibnizEQ State.state_initialize false);
      process args
  | NOTREPLACEANDREWSEQ :: args ->
      ignore(State.set_flag_replace_andrewsEQ State.state_initialize false);
      process args
  | NOTUSECHOICE :: args ->
      ignore(State.set_flag_use_choice State.state_initialize false);
      process args
  | NOTUSEEXTUNI :: args ->
      ignore(State.set_flag_use_extuni State.state_initialize false);
      process args
  | NOTUSE_EXTCNFCOMBINED :: args ->
      ignore(State.set_flag_use_extcnf_combined State.state_initialize false);
      process args
  | SCRIPTMODE :: args ->
      global_conf.interactive <- true;
      process args
  | SOS :: args ->
      ignore(State.set_flag_sos State.state_initialize false);
      process args
  | TIMEOUT n :: args ->
      (*NOTE the code below is left in case it affects the interactive mode. In automatic mode,
             the timeout behaviour of Leo2 is controlled by the strategy scheduling mechanism.*)
      let globaltmo  = (max 1 n) in
      (*ATP applied for between 1 and 25 seconds. The exact value is at most 30% of the global timeout
        if the sequence instructions (related to -t and -ns) are followed*)
      (*FIXME update atptmo when global_conf.time_slices is updated?*)
      let atptmo = (min 25 (max 1 (n / (global_conf.time_slices + 2)))) in 
      (*Timeout for each slice? Assumes each strategy is given an equal amount of time*)
      let localtmo = (max 1 (n / global_conf.time_slices)) in
       global_conf.global_timeout <- globaltmo; (*used to scale time slices for each schedule*)
       Interactive.set_original_timeout globaltmo;
       Interactive.set_timeout localtmo; (*FIXME relevant?*)
       ignore
        (State.set_flag_atp_timeout
         State.state_initialize atptmo);
       ignore
        (State.set_flag_max_local_time
         State.state_initialize localtmo); (*FIXME relevant?*)
       process args
  | TMPPATH s :: args ->
      Util.tmp_path := s;
      process args
  | TRANSLATION s :: args ->
      ignore(State.set_flag_fo_translation
               State.state_initialize
               (* This checks that the translation is indeed supported *)
               (Translation_general.print_translation (Translation_general.read_translation s)));
      process args
  | UNFOLDDEFSEARLY :: args ->
      ignore(State.set_flag_unfold_defs_early State.state_initialize true);
      process args
  | UNFOLDDEFSLATE :: args ->
      ignore(State.set_flag_unfold_defs_early State.state_initialize false);
      process args
  | VERBOSE :: args ->
      ignore(State.set_flag_verbose State.state_initialize true);
      process args
  | VERSION :: args ->
      version ()
  | ORDERING s :: args ->
      ignore(State.set_flag_termorder
               State.state_initialize
               (* This checks that the weighting is indeed supported *)
               (Orderings.ordering_of_string s));
      (*possible syntax idea for precedences (as done by E and others):
        weighting(val=VALUE,fun={x:y,...},...)
        FIXME currently order information not supported.
      *)
      process args
  | WRITEFOCLAUSES :: args ->
      ignore(State.set_flag_write_fo_like_clauses State.state_initialize true);
      process args
  | [] -> execute_conf ()

let leo_main () =
  (*POSIX signal number for "CPU time limit exceeded"*)
  let sigxcpu = 24
  in
    (*register signal handlers*)
    begin
      try
        ignore(Sys.signal Sys.sigquit
                 (Sys.Signal_handle
                    (fun _ ->
                       set_current_success_status None Force;
                       cleanup ();
                       raise (Termination None))));
        ignore(Sys.signal sigxcpu
                 (Sys.Signal_handle
                    (fun _ ->
                       set_current_success_status None ResourceOut;
                       cleanup ();
                       raise (Termination None))));
        ignore(Sys.signal Sys.sigvtalrm
                 (Sys.Signal_handle
                    (fun _ ->
                       assert global_conf.interactive;
                       (*if in interactive mode then preserve current behaviour*)
                       Interactive.handle_timeout ())));
      (*FIXME check if following exclusion affects zombies*)
      (*FIXME could make dependent on a DEBUG switch:
        ignore(Sys.signal Sys.sigchld Sys.Signal_ignore); *)
        let com_line = List.tl (Array.to_list Sys.argv) in
        let args = parse_cl com_line [] in
          process args
      with
        | Termination maybe_st ->
            (*Some unplanned exits pass through here: e.g. timeouts, errors*)
            begin
              Util.sysout 0 (State.szs_result maybe_st ^ "\n");
              exit (szs_exitcode ())
            end
        | e ->
            (*All other unplanned exists pass through here*)
            if e = Sys.Break then
              set_current_success_status None User
            else
              begin
                set_current_success_status None Error;
                prerr_endline ("\nError occurred:" ^ Printexc.to_string e);
                prerr_endline (Printexc.get_backtrace ())
              end;
            Util.sysout 0 (State.szs_result None ^ "\n");
            exit (szs_exitcode ())
    end;
    if not global_conf.interactive then
        exit (szs_exitcode ())

IFNDEF TOPLEVEL THEN leo_main () END
