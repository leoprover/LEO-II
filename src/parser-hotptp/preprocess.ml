(* ========================================================================= *)
(* TPTP preprocessor                                                         *)
(* ========================================================================= *)

(** Module Preprocess implements preprocessing for TPTP problem files
   @author Arnaud 
   @since 13-05-07 *)

let loadfile path file =
  let filename = if (Filename.is_relative file) 
                 then (Filename.concat path file) 
                 else file
  in
  Util.sysout 5 ("\n path: "^path^" file: "^file^" filename: "^filename);
  let chan = try open_in filename
             with _ ->
             try
             open_in ((Sys.getenv "TPTP")^file)
             with _ ->
             open_in ((Sys.getenv "TPTP")^"/"^file)
  in
  let rec rdl () =
    try(
      let line = input_line chan in
      line :: (rdl ())
    ) with End_of_file -> close_in chan; []
  in rdl ()

let rec strip_quotes s =
  if String.get s 0 = '\''
  then strip_quotes (String.sub s 1 (String.length s -1))
  else if String.get s (String.length s -1) = '\''
    then strip_quotes (String.sub s 0 (String.length s -1))
    else s
  
let is_include_statement s =
  try (
    if String.sub s 0 8 = "include("  
    then
        let endofname = try (String.index s ',') with Not_found -> String.index s ')' in
        let file = String.sub s 8 (endofname-8) in
        Some(strip_quotes file)
    else None
  ) with _ -> None
    
let rec expand path expanded outchan = function
    [] -> ()
  | line::ls -> 
    match is_include_statement line with
        Some(file) ->
      (*    print_string ("include :"^file^"\n"); *)
          if List.mem file expanded
          then failwith "circular inclusions"
          else (try expand path (file::expanded) outchan ((loadfile path file) @ ls)
                with e -> failwith ("could not open file "^path^"/"^file^": "^(Printexc.to_string e)^"\n"))
      | None -> output_string outchan (line^"\n"); expand path expanded outchan ls

(**
let get_dir_and_basename file =
  let lastslash = try (String.rindex file '/') with Not_found -> -1 in
  let (dir,base) =
    if lastslash > -1 then ( (String.sub file 0 lastslash)^"/", String.sub file (lastslash+1) (String.length file - lastslash - 1))
    else ("",file) in
  (dir,base)
**)

let expand_includes infile outfile =
  let (path,file) = (Filename.dirname infile, Filename.basename infile) in
  let inbuf = loadfile path file in  
  let outchan = open_out outfile in
  (try (
    expand path [infile] outchan inbuf
  ) with e -> print_string ("While preprocessing file "^infile^": "^(Printexc.to_string e)^"\n"); flush stdout);
  close_out outchan

