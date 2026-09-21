let debuglevel = ref 0

module StringSet = Set.Make(String)

let (tmpfiles : StringSet.t ref) = ref StringSet.empty
(*FIXME if child process are creating files, and run in parallel,
  then should distinguish files by using e.g. PID*)
let register_tmpfile file =
  let warn_s = "\nWARNING register_tmpfile applied again to " ^ file ^ "\n"
  in
    if StringSet.mem file !tmpfiles then
      prerr_endline warn_s
    else
      tmpfiles := StringSet.add file !tmpfiles
let register_tmpfiles files =
  List.iter register_tmpfile files
(*unregister_tmpfile is not called directly from the outside --
  use try_delete_file instead*)
let unregister_tmpfile file =
  let warn_s = "\nWARNING is unregister_tmpfile being reapplied to " ^ file ^ " ?\n"
  in
    if StringSet.mem file !tmpfiles then
      tmpfiles := StringSet.remove file !tmpfiles
    else
      prerr_endline warn_s

(*Scratch files go in a directory of this process's own, unless "--tmp" names
  one.  LEO-II builds every scratch name out of the problem's basename --
  "<tmp>/<basename>__expanded__", "<basename>.atp_in", and so on -- so two
  LEO-IIs running at once on two problems that happen to share a basename
  write, and then unlink, the same file, and the loser dies on a file it had
  every reason to expect.  That is not exotic: the TPTP and any dataset of
  variants are full of repeated basenames, and any harness that measures in
  parallel produces exactly this.  It showed up as one SZS status Error per
  few hundred problems, always on whichever problem was running when the
  collision happened, never reproducible on that problem alone.

  The directory is removed at exit whether it was used or not -- rmdir only
  succeeds on an empty one, so a run told to keep its files by "--tmp" keeps
  them and merely leaves this one, unused and empty, to be swept away.  A
  portfolio is where that matters: each branch is told where to write, so each
  branch's own directory stays empty, and without this a single run over 294
  problems left seventeen hundred of them behind.*)
let tmp_path =
  let base = try Sys.getenv "TMPDIR" with Not_found -> "/tmp" in
  let mine = Filename.concat base ("leo_" ^ string_of_int (Unix.getpid ())) in
    (try Unix.mkdir mine 0o700 with Unix.Unix_error _ -> ());
    ref (if Sys.file_exists mine then mine else base)
let own_tmp_dir = !tmp_path

let previous_output_supressed = ref false
let supressed_output_count = ref 0

let unix_err_handler (err, f, rest) =  f ^ ":\"" ^ Unix.error_message err  ^ "\""

let try_delete_file file =
  if Sys.file_exists file then
    begin
      try Unix.unlink file
      with Unix.Unix_error (err, f, rest) ->
        prerr_endline ("WARNING Could not delete temporary file \"" ^
                         file ^ unix_err_handler (err, f, rest))
    end;
  unregister_tmpfile file

let delete_all_tmpfiles () =
    StringSet.iter try_delete_file !tmpfiles

(*The process's own scratch directory goes at exit, however the process ends:
  cleanup is not reached on every path out, and a directory left behind for
  every run would fill the system's temporary directory over an afternoon of
  measuring.  Only if it is empty, so that nothing is taken away from a run
  that asked for its files to be kept.*)
let () =
  at_exit (fun () -> try Unix.rmdir own_tmp_dir with Unix.Unix_error _ -> ())

let sysout n s =
  if n <= !debuglevel
  then
    begin
      if !previous_output_supressed then print_string "\n";
      print_string s;
      flush stdout;
      previous_output_supressed := false
    end
  else
    begin
      if !supressed_output_count = 1000
      then
        begin
          print_string ".";
          flush stdout;
          supressed_output_count := 0;
          previous_output_supressed := true
        end
      else
        supressed_output_count := !supressed_output_count + 1
    end

(* The message is built only if it will be shown.  Most call sites pass a
   concatenation of rendered clauses or terms, which at the default verbosity
   was built and thrown away at every step of the innermost loops.  Passing
   "" to sysout in the other case keeps the suppressed-output accounting, and
   with it the progress dots, exactly as it was. *)
let sysoutf n f = if n <= !debuglevel then sysout n (f ()) else sysout n ""

let add_list ht k l =
        Hashtbl.add ht l

let add_elem ht k e =
        if Hashtbl.mem ht k then
          let l = Hashtbl.find ht k in
          if not (List.mem e l) then
            Hashtbl.replace ht k (e::l)
          else ()
        else Hashtbl.add ht k [e]

let remove_list ht k =
        Hashtbl.remove ht k

let remove_elem ht k e =
        if Hashtbl.mem ht k then
        let l = Hashtbl.find ht k in
        if List.mem e l then
        Hashtbl.replace ht k (List.filter (fun e' -> e != e') l)

let remove_elem2 ht k e =
        if Hashtbl.mem ht k then
        let l = Hashtbl.find ht k in
        if List.mem e l then
        let l' = List.filter (fun e' -> e != e') l in
        if l'=[] then Hashtbl.remove ht k
        else Hashtbl.replace ht k l'

let remove_element3 htbl a b =
  let l = ref [] in
  while Hashtbl.mem htbl a do
    l := (Hashtbl.find htbl a)::(!l);
    Hashtbl.remove htbl a
  done;
  List.iter (fun x -> if x != b then Hashtbl.add htbl a x) !l

let replace_element htbl a b c =
  remove_element3 htbl a b;
  Hashtbl.add htbl a c

let concat_unique l1 l2 =
  l1 @ (List.filter (fun x -> not (List.mem x l1)) l2)

let iteri f n =
  let rec iteri i =
    if i=n then []
    else (f i)::(iteri (i+1))
  in iteri 0

let id x = x

let implode glue pieces =
  List.fold_left (fun acc el -> acc^(if acc="" then "" else glue)^el) "" pieces


let clean_symbol s =
  let char_map c =
    let cc = Char.code c in
    if (cc >= (Char.code 'A') && cc <= (Char.code 'Z')) ||
       (cc >= (Char.code 'a') && cc <= (Char.code 'z')) ||
       (cc >= (Char.code '0') && cc <= (Char.code '9'))
    then String.make 1 c
    else
      match c with
        '.' -> "_"
      | '_' -> "_"
      | '$' -> "s_"
      | '@' -> "at_"
      | '#' -> "x_"
      | _ -> ("_"^(string_of_int (Char.code c))^"_")
  in
  let accu = ref "" in
  for i = 0 to (String.length s) -1 do
    accu := !accu^(char_map s.[i])
  done;
  !accu

(** migrated here from /src/extensions/pa_timed_enabled.ml : *)

let time_ht = Hashtbl.create 12

let start_timer (s:string) =
  try (
    let (_,total) = Hashtbl.find time_ht s in
      Hashtbl.replace time_ht s (Sys.time(),total)
  ) with Not_found -> Hashtbl.add time_ht s (Sys.time(),0.)

let stop_timer (s:string) =
  let (run,total) = Hashtbl.find time_ht s in
  let diff = Sys.time() -. run in
    Hashtbl.replace time_ht s (diff,total +. diff)

let get_total (s:string) =
  snd (Hashtbl.find time_ht s)

let get_all_totals () =
  let times = Hashtbl.fold (fun proc (_,time) acc -> (time,proc)::acc) time_ht [] in
    List.sort (fun (time1,_) (time2,_) -> compare time2 time1) times

(*child process groups*)
let child_processes: int list ref = ref []

(*start a child process, make it a process group, add its pid
  to child_processes*)
let spawn cmd =
  match Unix.fork () with
      0 ->
        ignore(Sys.signal Sys.sigchld Sys.Signal_default);
        (*create new process group and run command*)
        Build_config.setpgid_self ();
        let split_cmd = Str.split (Str.regexp " ") cmd
        in (try (Unix.execv (List.hd split_cmd) (Array.of_list split_cmd))
            with Unix.Unix_error (err, f, rest) ->
              (prerr_endline (unix_err_handler (err, f, rest))); -1)
    | pid ->
        sysout 2 ("\nspawned " ^ cmd ^ ";" ^
           "child has pid " ^ string_of_int pid ^ "\n");
        child_processes := pid :: !child_processes;
        pid

let waitfor_spawn cmd =
  let pid = spawn cmd
  in try (Unix.waitpid [] pid)
     with Unix.Unix_error (Unix.ECHILD, "waitpid", _) ->
          (*child has already terminated*)
          (pid, Unix.WEXITED 255) (*FIXME exit status unknown*)

(*wrapper for Sys.command, to reset SIGCHLD handling in the forked process*)
let command cmd =
  ignore(Sys.signal Sys.sigchld Sys.Signal_default);
  let exit_status = Sys.command cmd
  in
    ignore(Sys.signal Sys.sigchld Sys.Signal_ignore);
    exit_status

(*examine child processes*)
let nanny () =
  let ready_processes: int list ref = ref [] in
  let process_ended pid = (ready_processes := pid :: !ready_processes; true) in
  let nanny_filter pid =
    try(match (Unix.waitpid [Unix.WNOHANG] pid) with
          (0, _) -> false (*child hasn't died*)
         | _ -> process_ended pid)
    with Unix.Unix_error _ -> process_ended pid
  in
    child_processes := List.filter nanny_filter !child_processes;
    !ready_processes

(*kill all registered child process groups*)
let filicide_all () =
  let filicide pid =
    try (Unix.kill (-pid) Sys.sigkill)
    with Unix.Unix_error (err, f, rest) ->
      prerr_endline (unix_err_handler (err, f, rest))
  in
    List.iter filicide !child_processes;
    (*FIXME instead of clearing child_processes, remove only those processes
            which have terminated, or block until all those processes have terminated*)
    child_processes := []
