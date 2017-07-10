(* ========================================================================= *)
(* Positions and related data structures                                     *)
(* ========================================================================= *)


(** Module Position implements term positons and related data structures.
    @author Frank
    @since 19-05-06*)

(** To Do: replace entry lists and list operations by sets (list->set, append->union) *)


type relpos = Abstraction | Function | Arg

type position = relpos list

type 'a positiondata = NoData | WithData of 'a

type 'a positiontable = Empty |
                        Table of 'a positiontable *
                                  'a positiontable *
                                  'a positiontable *
                                  'a positiondata

let new_positiontable () = Empty

let new_primitive d = Table(Empty,Empty,Empty,WithData d)

let new_application f a = match f with
                            Table(_,_,_,_) -> Table(Empty,f,a,NoData) |
                            Empty -> (match a with
                                      Table(_,_,_,_) -> Table(Empty,Empty,a,NoData) |
                                      Empty -> Empty)           

let new_abstraction b = match b with
                            Table(_,_,_,d) -> Table(b,Empty,Empty,NoData) |
                            Empty -> Empty


let rec insert_at_pos table pos d =
  match table with
    Empty -> if List.length pos = 0
             then Table(Empty,Empty,Empty,WithData d)
             else (match List.hd pos with
              Abstraction -> Table(insert_at_pos Empty (List.tl pos) d,Empty,Empty,NoData) | 
              Function  -> Table(Empty,insert_at_pos Empty (List.tl pos) d,Empty,NoData) | 
              Arg   -> Table(Empty,Empty,insert_at_pos Empty (List.tl pos) d,NoData)) |
    Table(abstr,func,arg,d2) ->
             if List.length pos = 0
             then Table(abstr,func,arg,WithData d)
             else match List.hd pos with
              Abstraction -> Table(insert_at_pos abstr (List.tl pos) d,func,arg,d2) | 
              Function  -> Table(abstr,insert_at_pos func (List.tl pos) d,arg,d2) | 
              Arg   -> Table(abstr,func,insert_at_pos arg (List.tl pos) d,d2) 



let rec data_at_pos table pos =
  match table with
    Empty -> raise Not_found |
    Table(abstr,func,arg,d) ->
             if List.length pos = 0
             then (match d with
                    NoData -> raise Not_found |
                    WithData d2 -> d2) 
             else match List.hd pos with
              Abstraction -> data_at_pos abstr (List.tl pos) | 
              Function  -> data_at_pos func (List.tl pos) | 
              Arg   -> data_at_pos arg (List.tl pos) 
   

let rec all_entries' pos pt = match pt with
  Table(abstr,func,arg,d) -> let rest = (all_entries' (Abstraction::pos) abstr) @
                                        (all_entries' (Function::pos) func) @
                                        (all_entries' (Arg::pos) arg) in
                             (match d with
                               NoData -> rest |
                               WithData x -> (List.rev pos,x)::rest) |
  Empty -> []

let all_entries pt = all_entries' [] pt


let to_string pos = "["^(List.fold_right
                           (fun hd tl -> (match hd with
                                            Abstraction -> "abstr" |
                                            Function -> "func" |
                                            Arg -> "arg")^
                                         (match tl with
                                            "" -> "" |
                                            _ -> "; "^tl))
                           pos "")^"]"


let pstree_optional_args = "[levelsep=5ex,nodesep=3pt]"

let to_tex sf pt =
	let data_to_string = function
			NoData -> ""
		| WithData x -> sf x
	in
	let add_sep = function
			"" -> ""
		| s  -> ":"^s
	in
	let emptybranch = " \\psset{linestyle=none} \\TR{} \\psset{linestyle=solid}\n" in
	let rec draw_tree d branchlabel t =
		let w = String.make d ' ' in
		match t with
				Table(abstr,func,arg,pd) -> (
					match (abstr,func,arg) with
							(Empty,Empty,Empty) ->
								w^"\\TR{"^(data_to_string pd)^"}"^branchlabel^"\n"
								
						| (  _  ,Empty,Empty) ->						
								w^"\\pstree"^(if d=0 then pstree_optional_args else "")
							 	 ^"{\\TR{$\\lambda$"^(add_sep (data_to_string pd))^"}"^branchlabel^"}{\n"
							 	 ^(draw_tree (d+1) "" abstr)
							 	 ^w^"}\n"
							 
						| (Empty,Empty,  _  ) ->
								w^"\\pstree"^(if d=0 then pstree_optional_args else "")
							 	 ^"{\\TR{$@$"^(add_sep (data_to_string pd))^"}"^branchlabel^"}{\n"
							 	 ^w^emptybranch
							 	 ^(draw_tree (d+1) "" arg)
							 	 ^w^"}\n"
						
						| (Empty,  _  ,Empty) ->
								w^"\\pstree"^(if d=0 then pstree_optional_args else "")
							 	 ^"{\\TR{$@$"^(add_sep (data_to_string pd))^"}"^branchlabel^"}{\n"
							 	 ^(draw_tree (d+1) "" func)
							 	 ^w^emptybranch
							 	 ^w^"}\n"
						
						| (Empty,  _  ,  _  ) ->
								w^"\\pstree"^(if d=0 then pstree_optional_args else "")
							 	 ^"{\\TR{$@$"^(add_sep (data_to_string pd))^"}"^branchlabel^"}{\n"
							 	 ^(draw_tree (d+1) "" func)
							 	 ^(draw_tree (d+1) "" arg)
							 	 ^w^"}\n"
						
						| (  _  ,  _  ,  _  ) ->
								w^"\\pstree"^(if d=0 then pstree_optional_args else "")
							 	 ^"{\\TR{"^(data_to_string pd)^"}"^branchlabel^"}{\n"
							 	 ^(draw_tree (d+1) " \\tlput{\\tiny{abstr}} " abstr)
							 	 ^(draw_tree (d+1) " \\tvput{\\tiny{func}} " func)
							 	 ^(draw_tree (d+1) " \\trput{\\tiny{arg}} " arg)
							 	 ^w^"}\n"
					)
			| Empty -> ""
	in
	(draw_tree 0 "" pt)^"\n\n\\vspace{1cm}\n"




let show_all_entries sf pt = match pt with
                               Empty -> "empty positiontable\n" |
                               _ -> "positiontable:\n"^(List.fold_right
                                      (fun (pos,x) r -> (to_string pos)^" : "^(sf x)^"\n"^r)
                                      (all_entries pt)
                                      "end.\n")


let rec merge tablst = match tablst with
                         [] -> Empty |
                         _ :: _ ->
                           let accumulate a b = (match a with Empty -> b |
                                                              _ -> a::b) in
                           let subpos = List.fold_right
                                          (fun a b -> match (a,b) with
                                               (Empty,r) -> r |
                                               (Table(a,b,c,d),(ar,br,cr,dr)) -> ((accumulate a ar),
                                                                                  (accumulate b br),
                                                                                  (accumulate c cr),
                                                                                  (if d = NoData then dr else d)))
                                          tablst
                                          ([],[],[],NoData) in
                           match subpos with (a,b,c,d) -> Table(merge a,merge b,merge c,d)

let rec replace pt1 pt2 = match pt1 with
                            Empty -> Empty |
                            Table(a,b,c,d) -> (match d with
                                                 NoData -> Table((replace a pt2),
                                                                 (replace b pt2),
                                                                 (replace c pt2),d) |
                                                 WithData _ -> pt2)

let rec modify pt1 f = match pt1 with
                            Empty -> Empty |
                            Table(a,b,c,d) -> Table((modify a f),
                                                    (modify b f),
                                                    (modify c f),
                                                    (match d with NoData -> NoData |
                                                                  WithData d -> WithData (f d)))
                   


let rec size_of pt = match pt with
                       Empty ->0 |
                       (* Table(Empty,Empty,Empty,NoData) -> (print_string "Empty nonprimitive table!\n";1) |*)
                       Table(a,b,c,_) -> 1+ (size_of a) + (size_of b) + (size_of c)

(*
let rec all_occurrences table =
  match !table with
    Empty -> [] |
    Table(abstr,func,arg,l) ->
      all_occurrences abstr @
      all_occurrences func @
      all_occurrences arg @
      !l

let rec subterms_at table pos =
  match !table with
    Empty -> [] |
    Table(abstr,func,arg,l) ->
      if List.length pos = 0
      then !l
      else
        match List.hd pos with
          Abstraction -> subterms_at abstr (List.tl pos) |
          Function  -> subterms_at func (List.tl pos) |
          Arg   -> subterms_at arg (List.tl pos)

let rec subterms_below table pos =
  match !table with
    Empty -> [] |
    Table(abstr,func,arg,l) ->
      if List.length pos = 0
      then all_occurrences table
      else
        match List.hd pos with
          Abstraction -> subterms_below abstr (List.tl pos) |
          Function  -> subterms_below func (List.tl pos) |
          Arg   -> subterms_below arg (List.tl pos)

let rec subterms_above table pos =
  match !table with
    Empty -> [] |
    Table(abstr,func,arg,l) ->
      if List.length pos = 0
      then []
      else
        !l@
        match List.hd pos with
          Abstraction -> subterms_above abstr (List.tl pos) |
          Function  -> subterms_above func (List.tl pos) |
          Arg   -> subterms_above arg (List.tl pos)


let insert_superterm_at table pos v = insert_subterm_at table (List.rev pos) v

let superterms_at table pos = subterms_at table (List.rev pos)

let superterms_no_closer_than table pos = subterms_below table (List.rev pos)

let superterms_no_farther_than table pos = subterms_above table (List.rev pos)

*)
