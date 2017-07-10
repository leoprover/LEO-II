(* ========================================================================= *)
(* Advanced command-line interface                                           *)
(* ========================================================================= *)

(** Module Cmdline implements a command-line interface with line editing functions
   @author Arnaud
   @since 29-03-07 *)

open List
open State

type filetype = FNone | FDir | FExt of string list
type argtype = AInt | AStr | AFile of filetype

type arginfo = {
  argtype : argtype;
  argname : string;
  argrequired : bool;
  arghistcontext : int;
  argstrvalues : string list
}

type argdata = IntArg of int | StrArg of string | FileArg of string

type command = string * string * arginfo list * (argdata list -> bool)

type token = Ascii of char | Enter | ArrowUp | ArrowDown | ArrowRight | ArrowLeft | KeyEnd | KeyHome | KeyDel | Tab | Backspace | Esc | Ignore


(* global variables ---------------- *)

let interactive = ref false
let line = ref ""
let pos = ref 0
let history_contexts = Hashtbl.create 10
let history_pos = ref (-1)
let original_line = ref None
let empty_newlines = ref true
let commands = ref []
let saved_tcio = ref 
   {Unix.c_ignbrk = false; Unix.c_brkint = false; Unix.c_ignpar = false;
    Unix.c_parmrk = false; Unix.c_inpck = false; Unix.c_istrip = false;
    Unix.c_inlcr = false; Unix.c_igncr = false; Unix.c_icrnl = true;
    Unix.c_ixon = false; Unix.c_ixoff = false; Unix.c_opost = true;
    Unix.c_obaud = 38400; Unix.c_ibaud = 38400; Unix.c_csize = 8;
    Unix.c_cstopb = 1; Unix.c_cread = true; Unix.c_parenb = false;
    Unix.c_parodd = false; Unix.c_hupcl = false; Unix.c_clocal = false;
    Unix.c_isig = true; Unix.c_icanon = true; Unix.c_noflsh = false;
    Unix.c_echo = true; Unix.c_echoe = true; Unix.c_echok = true;
    Unix.c_echonl = false; Unix.c_vintr = '\003'; Unix.c_vquit = '\028';
    Unix.c_verase = '\127'; Unix.c_vkill = '\021'; Unix.c_veof = '\004';
    Unix.c_veol = '\000'; Unix.c_vmin = 1; Unix.c_vtime = 0;
    Unix.c_vstart = '\017'; Unix.c_vstop = '\019'}

let save_tcio () =
  saved_tcio := Unix.tcgetattr Unix.stdin

let get_int_arg = function
    (IntArg i)::xr -> (i,xr)
  | _ -> failwith "get_int_arg"

let get_str_arg = function
    (StrArg s)::xr -> (s,xr)
  | _ -> failwith "get_str_arg"

let get_file_arg = function
    (FileArg f)::xr -> (f,xr)
  | _ -> failwith "get_file_arg"


let mkarg ?(required=true) ?(histcontext=(-1)) ?(strvalues=[]) aty s = {
  argtype=aty;
  argname=s;
  argrequired=required;
  arghistcontext=histcontext;
  argstrvalues=strvalues
}

let set_commands cs =
  commands := cs

let add_command c =
  commands := c :: !commands

let get_commands () =
  !commands

(* tab completion functions ---------------- *)
let cmd_get_command (cmd,_,_,_) = cmd
let cmd_get_descr (_,descr,_,_) = descr
let cmd_get_args (_,_,args,_) = args
let cmd_get_func (_,_,_,func) = func

let largest_common_prefix s1 s2 =
  let minlen = min (String.length s1) (String.length s2) in
  let rec scan i =
    if i>=minlen
    then ""
    else
      if String.get s1 i = String.get s2 i
      then (String.make 1 (String.get s1 i))^(scan (i+1))
      else ""
 in scan 0

let command_get_args cmd =
  fold_left (fun acc (c,_,args,_) -> if c=cmd then Some args else acc) None !commands

let matching_commands s =
  filter (fun (cmd,_,_,_) -> String.length cmd >= String.length s && String.sub cmd 0 (String.length s) = s) !commands

let cmd_descr (c,s,_,_) = c^s

let complete_command s =
  let mc = matching_commands s in
  let cd = map cmd_descr mc in
  match mc with
    [] -> (s,[]) |
    [(c,s,_,_)] -> (c^" ",cd) |
    (c,s,_,_)::xr -> (fold_left largest_common_prefix c (map cmd_get_command xr),cd)

let matching_strings s sl =
  filter (fun s' -> String.length s' >= String.length s && String.sub s' 0 (String.length s) = s) sl

let get_dir_contents filetype dir =
  let dir = (if dir="" then "." else dir) in
  let dh = Unix.opendir dir in
  let rec getfiles () =
    try (
      let fn = Unix.readdir dh in
      if (Unix.stat (Filename.concat dir fn)).Unix.st_kind=Unix.S_DIR
      then (fn^"/") :: getfiles ()
      else fn :: getfiles ()
    ) with End_of_file -> []
  in
  let has_ext fn e =
    e="" || Filename.check_suffix fn ("."^e)
  in
  List.sort (fun fn1 fn2 ->
    if fn1="./" || (fn1="../" && fn2<>"./") then -1
    else if fn2="./" || (fn2="../" && fn1<>"./") then 1
      else if String.get fn1 (String.length fn1 -1) = '/' then
        if String.get fn2 (String.length fn2 -1) = '/' then
          String.compare fn1 fn2
        else -1
      else
        if String.get fn2 (String.length fn2 -1) = '/' then 1
        else String.compare fn1 fn2)
    (filter (fun fn ->
      let isdir = String.get fn (String.length fn -1) = '/' in
      match filetype with
          FDir -> isdir
        | FExt es -> isdir || (List.exists (has_ext fn) es)
        | FNone -> true
    ) (getfiles ()))

let complete_filename ?(filetype=FNone) s =
  let lastslash = try (String.rindex s '/') with Not_found -> -1 in
  let (dir,base) =
    if lastslash > -1 then ( (String.sub s 0 lastslash)^"/", String.sub s (lastslash+1) (String.length s - lastslash - 1))
    else ("",s) in
    let mc = matching_strings base (get_dir_contents filetype dir) in
    match mc with
      [] -> (s,[]) |
      [c] -> (Filename.concat dir c,mc) |
      c::cr -> (Filename.concat dir (fold_left largest_common_prefix c cr),mc)

let complete_str sl s =
  let ms = matching_strings s sl in
  match ms with
    [] -> (s,[]) |
    [t] -> (t^" ",ms) |
    t::tr -> (fold_left largest_common_prefix t tr,ms)

(* line editing functions ---------------- *)
let readtoken () =
  match input_char stdin with
      '\027' -> (
        match input_char stdin with
            '[' -> (
              match input_char stdin with
                  'A' -> ArrowUp
                | 'B' -> ArrowDown
                | 'C' -> ArrowRight
                | 'D' -> ArrowLeft
                | 'F' -> KeyEnd
                | 'H' -> KeyHome
                | '\051' -> (
                    match input_char stdin with
                        '\126' -> KeyDel
                      |   c    -> Ignore)
                | c  -> Ignore)
         | '\027' -> Esc
         |  c   -> Ascii c)
   | '\009' -> Tab
   | '\127' -> Backspace
   | '\010' -> Enter
   | c -> Ascii c

let token2string = function
    Ascii c -> String.make 1 c
  | ArrowUp -> "Up"
  | ArrowDown -> "Down"
  | ArrowRight -> "Right"
  | ArrowLeft -> "Left"
  | KeyEnd -> "End"
  | KeyHome -> "Home"
  | KeyDel -> "Del"
  | Tab -> "Tab"
  | Backspace -> "Backspace"
  | Enter -> "Enter"
  | Esc -> "Esc"
  | Ignore -> ""

let movecursor_right n =
  for i = 0 to n-1 do
    let p = !pos+i in
    if p < String.length !line
    then output_char stdout (String.get !line p)
    else output_char stdout ' '
  done

let movecursor_left n =
  for i = 1 to n do
    output_char stdout '\b'
  done

let setline s =
  movecursor_left !pos;
  for i = 1 to String.length !line do
    output_char stdout ' '
  done;
  movecursor_left (String.length !line);
  line := s;
  pos := String.length s;
  output_string stdout s

let start_edit () =
  if (!interactive) then
  (
    (* print_string "Hey, I'm interactive!\n"; *)
    save_tcio ();
    let tcio = Unix.tcgetattr Unix.stdin in
    tcio.Unix.c_echo <- false;
    tcio.Unix.c_icanon <- false;
    tcio.Unix.c_vmin <- 1;
    (*tcio.Unix.c_isig <- false;*)
    (*tcio.Unix.c_ixon <- false;*)
    Unix.tcsetattr Unix.stdin Unix.TCSADRAIN tcio
  )
  else ()

let end_edit () =
  if (!interactive)
  then Unix.tcsetattr Unix.stdin Unix.TCSADRAIN !saved_tcio
  else ()

let insert_text s =
  if !pos < String.length !line
  then (
    let s1 = String.sub !line 0 !pos in
    let s2 = String.sub !line !pos (String.length !line - !pos) in
    output_string stdout s;
    output_string stdout s2;
    line := s1^s^s2;
    pos := !pos + (String.length s);
    for i = 1 to String.length s2 do
      output_char stdout '\b'
    done
  ) else (
    line := !line^s;
    pos := !pos + (String.length s);
    output_string stdout s
  )

let which_word () =
  let count = ref 0 in
  for i = 0 to !pos-1 do
    if String.get !line i = ' '
    then count := !count + 1
    else ()
  done;
  !count

let expected_arg () =
  let whichword = which_word () in
  if whichword=0 then None else
    let cmd = String.sub !line 0 (String.index !line ' ') in
    match command_get_args cmd with
        Some(args) -> (try (Some (nth args (whichword-1))) with _ -> None)
      | None -> None

let implode glue pieces =
  fold_left (fun acc el -> acc^(if acc="" then "" else glue)^el) "" pieces

let split c s =
  if s = "" then [] else
  let accum = ref [] in
  let len = String.length s in
  let i = ref (len-1) in
  try
    while true do
      let nextc = String.rindex_from s !i c in
      let s = if nextc < !i then String.sub s (nextc+1) (!i-nextc) else "" in
      accum := s::!accum;
      i := nextc-1;
    done;
    !accum
  with
    Not_found ->
      (String.sub s 0 (!i+1))::!accum

let valOf = function
    Some a -> a
  | None -> failwith "valOf"


let matching_lparen pos rparen =
  let lparen =
    match rparen with
      ')' -> '('
    | ']' -> '['
    | '}' -> '{'
    | _ -> failwith "undefined paren"
  in
  let scope = ref 0 in
  let result = ref (-1) in
  for i = pos downto 0 do
    let a = String.get !line i in
    if a=rparen
    then scope := !scope + 1
    else if a=lparen
         then if !scope=0 && !result<0
              then result := i
              else scope := !scope - 1
         else ()
  done;
  if !result>=0 then Some(!result) else None

let matching_rparen pos lparen =
  let rparen =
    match lparen with
      '(' -> ')'
    | '[' -> ']'
    | '{' -> '}'
    | _ -> failwith "undefined paren"
  in
  let scope = ref 0 in
  let result = ref (-1) in
  for i = pos to String.length !line -1 do
    let a = String.get !line i in
    if a=lparen
    then scope := !scope + 1
    else if a=rparen
         then if !scope=0 && !result<0
              then result := i
              else scope := !scope - 1
         else ()
  done;
  if !result>=0 then Some(!result) else None


let inplace_complete prefix cursorword suffix =
  let expand = function
      "thf" | "fof" | "cnf" -> "(name,role,formula)."
    | "thf(" | "fof(" | "cnf(" -> "name,role,formula)."
    | _ -> raise Not_found
  in
  try (
    let compl = expand cursorword in
    if compl<>suffix
    then
      let p = !pos in
      setline (prefix^cursorword^compl^suffix);
      movecursor_left (String.length (compl^suffix));
      pos := p;
      ("",[])
    else ("",[])
  ) with Not_found -> (cursorword,[]) (*complete_command cursorword (* this is not clean. might need ACommand *)*)

exception Escape_pressed

let getline ?(expectedtype=None) ?(raise_esc=false) ?(history_context=0) ?(strvalues=[]) prompt =
  start_edit ();
  output_string stdout prompt;
  flush stdout;
  let history = ref (if history_context>=0 then try (Hashtbl.find history_contexts history_context) with Not_found -> [] else []) in
  let save_history () =
    if history_context>=0
    then Hashtbl.replace history_contexts history_context !history
    else () in
  try (
    let theline = ref "&&02/&&%" in
    while !theline="&&02/&&%" do
      let _ =
        match readtoken () with
            Ascii c ->
              insert_text (String.make 1 c); original_line := None; history_pos := -1;
              if !pos>1 && (c=')' || c=']' || c='}')
              then (
                match matching_lparen (!pos-2) c with
                    Some i -> (
                      flush stdout;
                      let d = !pos-i in
                      movecursor_left d;
                      pos := i;
                      flush stdout;
                      ignore(Unix.select [Unix.stdin] [] [] 1.0);
                      movecursor_right d;
                      pos := !pos + d;
                      flush stdout )
                  | None -> ()
                )
              else if c='(' || c='[' || c='{'
              then (
                match matching_rparen !pos c with
                    Some i -> (
                      flush stdout;
                      let d = i - !pos in
                      movecursor_right d;
                      pos := i;
                      flush stdout;
                      ignore(Unix.select [Unix.stdin] [] [] 1.0);
                      movecursor_left d;
                      pos := !pos - d;
                      flush stdout )
                  | None -> ()
                )
          | Backspace ->
              if !pos < String.length !line && !pos > 0
              then (
                let s1 = String.sub !line 0 !pos in
                let s2 = String.sub !line !pos (String.length !line - !pos) in
                output_char stdout '\b';
                output_string stdout s2;
                output_char stdout ' ';
                output_char stdout '\b';
                line := (String.sub s1 0 (String.length s1 -1))^s2;
                pos := !pos - 1;
                movecursor_left (String.length s2)
              )
              else if !pos > 0 then (
                output_char stdout '\b';
                output_char stdout ' ';
                output_char stdout '\b';
                line := String.sub !line 0 (String.length !line -1);
                pos := !pos - 1
              ) else ()
          | Enter ->
              if !empty_newlines || String.length !line > 0
              then output_char stdout '\n'
              else ();
              if history_context>=0 && String.length !line > 0 && (!history=[] || !line <> hd !history)
              then history := !line :: !history
              else ();
              history_pos := -1;
              original_line := None;
              theline := !line;
              line := "";
              pos := 0
          | ArrowUp ->
              if List.length !history > 0 then (
                if !original_line = None then original_line := Some !line else ();
                if !history_pos < length !history -1 then
                  history_pos := !history_pos + 1
                else ();
                let item = nth !history !history_pos in
                setline item)
              else ()
          | ArrowDown ->
              if !original_line = None then ()
              else (
                if !history_pos > 0 then (
                  history_pos := !history_pos - 1;
                  let item = nth !history !history_pos in
                  setline item
                ) else (
                  history_pos := -1;
                  setline (valOf !original_line)
                )
              )
          | ArrowLeft ->
              if !pos>0
              then
                let _ = pos := !pos -1 in
                output_char stdout '\b'
              else ()
          | ArrowRight ->
              if !pos<String.length !line
              then
                let _ = movecursor_right 1 in
                pos := !pos +1
              else ()
          | KeyHome ->
              movecursor_left !pos;
              pos := 0
          | KeyEnd ->
              if !pos<String.length !line then (
                movecursor_right (String.length !line - !pos);
                pos := String.length !line
              ) else ()
          | KeyDel ->
              if !pos < String.length !line
              then (
                let s1 = String.sub !line 0 !pos in
                let s2 = String.sub !line (!pos+1) (String.length !line - !pos -1) in
                output_string stdout s2;
                output_char stdout ' ';
                output_char stdout '\b';
                line := s1^s2;
                movecursor_left (String.length s2))
              else ()
          | Tab ->
              let cursorword_start =
                try (String.rindex_from !line (!pos-1) ' ' + 1)
                with Not_found -> 0 in
              let prefix = String.sub !line 0 cursorword_start in
              let cursorword = String.sub !line cursorword_start (!pos - cursorword_start) in
              let suffix = String.sub !line !pos (String.length !line - !pos) in
              let (comp,lst) =
                if expectedtype=None then
                  let ea=expected_arg () in
                  if ea <> None then
                    let ea=valOf(ea) in
                    match ea.argtype with
                        AFile ft -> complete_filename ~filetype:ft cursorword
                      | AStr ->
                          if strvalues <> []
                          then complete_str strvalues cursorword
                          else if ea.argstrvalues <> []
                            then complete_str ea.argstrvalues cursorword
                            else inplace_complete prefix cursorword suffix
                      | _ -> (cursorword,[])
                  else complete_command cursorword
                else
                  match expectedtype with
                      Some (AFile ft) -> complete_filename ~filetype:ft cursorword
                    | Some AStr ->
                        if strvalues <> []
                        then complete_str strvalues cursorword
                        else inplace_complete prefix cursorword suffix (*(cursorword,[])*)
                    | _ -> (cursorword,[])
              in
              if length lst = 0 then ()
              else if comp=cursorword then (
                  (* don't change line, print matching strings *)
                  movecursor_right (String.length !line - !pos);
                  output_char stdout '\n';
                  iter (fun l ->
                    output_string stdout (" "^l^"\n");
                  ) lst;
                  output_string stdout prompt;
                  output_string stdout !line;
                  for i = 1 to (String.length !line - !pos) do
                    output_char stdout '\b'
                  done
                ) else (
                  (* cut out incomplete word and insert completion *)
                  line := prefix^suffix;
                  pos := cursorword_start;
                  movecursor_left (String.length cursorword);
                  insert_text comp
                )
          | Esc ->
              if raise_esc then raise Escape_pressed else ()
          | _ -> ()
      in
        flush stdout
    done;
    end_edit ();
    save_history ();
    !theline
  ) with
      Escape_pressed -> end_edit (); save_history (); raise Escape_pressed
    | Sys.Break -> end_edit (); save_history (); raise Sys.Break
    | _ -> end_edit (); save_history (); ""


exception Bad_command

let execute_command s =
  let add_to_history hc line =
    if hc >= 0 && String.length line > 0 then
      let history = try Hashtbl.find history_contexts hc with Not_found -> []
      in if history=[] || line <> hd history then Hashtbl.replace history_contexts hc (line::history) in
  let words = filter (fun w -> String.length w > 0) (split ' ' s) in
  let (cmd, _, args, func) =
    try
      find (fun (c, _, _, _) -> c = hd words) !commands
    with Not_found ->
      prerr_endline ("Could not find command '" ^ hd words ^"' (Full command: '" ^
                       s ^ "')\n");
      raise Bad_command
  in
  let arguments = ref [] in
  let rec fill_args given expected =
    match (given, expected) with
        ([], []) -> ()
      | (g :: gr, []) ->
          print_string ("ignored arguments " ^ implode " " given ^ "\n");
          flush stdout
      | ([], e :: er) ->
          if e.argrequired then
            begin
              let input = getline
                ~expectedtype:(Some e.argtype)
                ~raise_esc:true
                ~history_context:e.arghistcontext
                ~strvalues:e.argstrvalues ("Please specify " ^ e.argname ^ ": ")
              in
                (* don't split string arguments at spaces *)
                if e.argtype=AStr then
                  fill_args [input] expected
                else
                  fill_args (filter (fun w -> String.length w > 0) (split ' ' input)) expected
            end
      | (g :: gr, e :: er) ->
          match e.argtype with
              AInt ->
                arguments := IntArg (int_of_string g) :: !arguments;
                add_to_history e.arghistcontext g;
                fill_args gr er
            | AStr ->
                arguments := StrArg g :: !arguments;
                add_to_history e.arghistcontext g;
                fill_args gr er
            | AFile _ ->
                arguments := FileArg g :: !arguments;
                add_to_history e.arghistcontext g;
                fill_args gr er in
    try
      fill_args (tl words) args;
      func !arguments
    with
        Escape_pressed ->
          print_string "cancel\n";
          flush stdout;
          true
      | Failure s as e ->
          if global_conf.interactive then
            begin
              print_string (s ^ "\n");
              flush stdout;
              false
            end
          else
            raise e
      | Sys_error s as e ->
          (*Small hack to avoid being thrown out of interactive mode
            when specific exceptions are raised*)
          let nsfod = "No such file or directory" in
          let nsfod_sz = String.length nsfod
          in
            if global_conf.interactive &&
              String.sub s (String.length s - nsfod_sz) (nsfod_sz) = nsfod then
                begin
                  print_string "Exception: File/dir not found\n";
                  flush stdout;
                  false
                end
            else
              raise e
