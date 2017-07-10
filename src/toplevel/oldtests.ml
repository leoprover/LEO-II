(* ========================================================================= *)
(* This is the main file                                                     *)
(* ========================================================================= *)

(* only some tests so far *)

open Hol_type
open Signature
open Term
open Termset

(** Test 1: generic tests for termset *)
let test1 () =
  print_string "\nTest 1: testing termset\n";
  
  print_string "generating signature...\n";
  let sigma = new_signature () in
  
  let bt = basetype in
  let tv_x = bt "X" in

  print_string "adding symbols p, +...\n\n";
  add_uninterpreted_symbol sigma "+" (abstr_type tv_x (abstr_type tv_x tv_x));
  add_uninterpreted_symbol sigma "p" (abstr_type tv_x bt_o);

  print_string "creating termset...\n";
  let ts = new_termset () in
 
  let t =
    Abstr(Symbol "x", tv_x,
      Appl(Symbol "p", Appl(Appl(Symbol "+", Symbol "x"),Symbol "x"))) in

  print_string ("adding term: "^(Term.to_string t)^"\n");
  let id = create ts t in
  print_string ("->index: "^(string_of_int id)^"\n\n");
  
  print_string "termset:\n";
  print_string (Termset.to_string ts);


  print_string "\nchecking node types:\n";
  print_string ("node_type(6): "^(Hol_type.to_string (Termset.node_type ts 6))^"\n");
  print_string ("node_type(2): "^(Hol_type.to_string (Termset.node_type ts 2))^"\n");

  print_string "termset:\n";
  print_string (Termset.to_string ts)

(** Test 2: beta-reduction of Church numerals *)
let test2 () =
  print_string "\nTest 2: beta-reduction of Church numerals\n";

  print_string "\ncreating termset...\n\n";
  let ts = new_termset () in

  let numeraltype = abstr_type (abstr_type bt_i bt_i) (abstr_type bt_i bt_i) in

  let zero = Abstr(Symbol "f", abstr_type bt_i bt_i, Abstr(Symbol "x", bt_i, Symbol "x")) in

  let succ = Abstr(Symbol "n", numeraltype, Abstr(Symbol "f", abstr_type bt_i bt_i, Abstr(Symbol "x", bt_i,
    Appl(Symbol "f", Appl( Appl(Symbol "n", Symbol "f"), Symbol "x"))))) in
  
  let plus = Abstr(Symbol "m", numeraltype, Abstr(Symbol "n", numeraltype, Abstr(Symbol "f", (abstr_type bt_i bt_i), Abstr(Symbol "x", bt_i,
    Appl( Appl(Symbol "m", Symbol "f"), Appl( Appl(Symbol "n", Symbol "f"), Symbol "x")))))) in

  print_string ("adding term zero: "^(Term.to_string zero)^"\n");
  let id_zero = create ts zero in
  print_string ("->index: "^(string_of_int id_zero)^"\n\n");
  
  print_string ("adding term succ: "^(Term.to_string succ)^"\n");
  let id_succ = create ts succ in
  print_string ("->index: "^(string_of_int id_succ)^"\n\n");
  
  print_string ("adding term plus: "^(Term.to_string plus)^"\n");
  let id_plus = create ts plus in
  print_string ("->index: "^(string_of_int id_plus)^"\n\n");

  (*
  print_string "termset:\n";
  print_string (Termset.to_string ts);
  *)
  
  print_string ("retrieve("^(string_of_int id_zero)^"): "^(Term.to_string (retrieve ts id_zero))^"\n");
  print_string ("retrieve("^(string_of_int id_succ)^"): "^(Term.to_string (retrieve ts id_succ))^"\n");
  print_string ("retrieve("^(string_of_int id_plus)^"): "^(Term.to_string (retrieve ts id_plus))^"\n");

  let one = Appl(succ,zero) in
  print_string ("\nadding term succ(zero): "^(Term.to_string one)^"\n");
  let id_one = create ts one in
  print_string ("->index: "^(string_of_int id_one)^"\n\n");

  print_string ("retrieve("^(string_of_int id_one)^"): "^(Term.to_string (retrieve ts id_one))^"\n");

  (* print_string ("\nBUG: the inner (((lambda [x2]: lambda [x3]: x3) x0) x1) is not beta-reduced\n\n");

   fixed *)

  let two = Appl(succ,one) in
  let oneplustwo = Appl(Appl(plus,one),two) in

  print_string ("\nadding term ((plus one) two): "^(Term.to_string oneplustwo)^"\n");
  let id_oneplustwo = create ts oneplustwo in
  print_string ("->index: "^(string_of_int id_oneplustwo)^"\n\n");

  print_string ("retrieve("^(string_of_int id_oneplustwo)^"): "^(Term.to_string (retrieve ts id_oneplustwo))^"\n");

  
  print_string "done"



(** Test 3: head-normalization by Termset.create *)
let test3 () =
  print_string "\nTest 3: head normal form\n";

  let sigma = new_signature () in
  let ts = new_termset () in

  let ty_f = abstr_type (abstr_type bt_i bt_i) (abstr_type bt_i (abstr_type bt_i bt_i)) in
  let ty_g = abstr_type (abstr_type bt_i (abstr_type bt_i bt_i)) (abstr_type (abstr_type bt_i bt_i) (abstr_type bt_i bt_i)) in
  let ty_h = abstr_type bt_i (abstr_type bt_i bt_i) in
  let ty_j = abstr_type bt_i bt_i in

  print_string "\nadding symbols:\n";  
  print_string ("f: "^(Hol_type.to_string ty_f)^"\n");
  add_uninterpreted_symbol sigma "f" ty_f;
  print_string ("g: "^(Hol_type.to_string ty_g)^"\n");
  add_uninterpreted_symbol sigma "g" ty_g;
  print_string ("h: "^(Hol_type.to_string ty_h)^"\n");
  add_uninterpreted_symbol sigma "h" ty_h;
  print_string ("j: "^(Hol_type.to_string ty_j)^"\n");
  add_uninterpreted_symbol sigma "j" ty_j;

  let t = Appl(Symbol "f", Appl(Appl(Symbol "g", Abstr(Symbol "x", bt_i, Appl(Symbol "h", Symbol "x"))), Symbol "j")) in

  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");

  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n");
  
  print_string "\neta-expanding...\n";
  let id_t_ee = eta_expand sigma ts id_t in
  print_string ("->index: "^(string_of_int id_t_ee)^"\n\n");
  
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t_ee)^"): "^(Term.to_string (retrieve ts id_t_ee))^"\n")
    

(** Test 4: still alive? *)
let test4 () =
  print_string "\nTest 4: deBruijn\n";

  let ts = new_termset () in

  let t=Appl(Abstr(Symbol"x", bt_i, Abstr(Symbol "y", bt_i, Appl(Abstr (Symbol "z",bt_i,Symbol "z"), Symbol "x"))),Abstr(Symbol "u",bt_i,Symbol "a")) in
  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n");


  let t=Appl(Abstr(Symbol"x", bt_i, Abstr(Symbol "y", bt_i, Appl(Abstr (Symbol "z",bt_i,Symbol "z"), Symbol "x"))),Abstr(Symbol "u",bt_i,Symbol "x")) in
  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n");
  

  let t=Abstr(Symbol "a",bt_i,Appl(Symbol "f",Appl(Symbol "h",Appl(Abstr(Symbol"x", bt_i, Abstr(Symbol "y", bt_i, Appl(Abstr (Symbol "z",bt_i,Symbol "z"), Appl(Symbol "x",Symbol "x")))),Abstr(Symbol "u",bt_i,Symbol "a"))))) in
  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n");


  let t=Appl(Symbol "f",Appl(Symbol "h",Appl(Abstr(Symbol"x", bt_i, Abstr(Symbol "y", bt_i, Appl(Abstr (Symbol "z",bt_i,Symbol "z"), Appl(Symbol "x",Symbol "x")))),Abstr(Symbol "u",bt_i,Symbol "a")))) in
  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n");


  let t=Appl(Symbol "f",Appl(Symbol "h",Appl(Abstr(Symbol"x", bt_i, Abstr(Symbol "y", bt_i, Appl(Abstr (Symbol "z",bt_i,Symbol "z"), Appl(Symbol "y",Symbol "x")))),Abstr(Symbol "u",bt_i,Symbol "a")))) in
  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n");



  let t=Appl(Symbol "f",Appl(Symbol"f",Abstr(Symbol"f",bt_i,Appl(Symbol "f",Abstr(Symbol "f",bt_i,Symbol "a"))))) in
  print_string ("\nadding term: "^(Term.to_string t)^"\n");
  let id_t = create ts t in
  print_string ("->index: "^(string_of_int id_t)^"\n\n");
  print_string "termset:\n";
  print_string (Termset.to_string ts);

  print_string ("\nretrieve("^(string_of_int id_t)^"): "^(Term.to_string (retrieve ts id_t))^"\n")


(** Test 5: still alive? *)
let test5 () =
  print_string "\nTest 4: 10x10x10\n";

  let ts = new_termset () in

  let rec church_num'(n) = (match n with 0 -> Symbol "x"
                                      | _ -> Appl(Symbol "f",church_num'(n-1)))
  in

  let church_num(n) =  Abstr(Symbol "f", abstr_type bt_i bt_i, Abstr(Symbol "x", bt_i, church_num'(n))) in

  let numeraltype = abstr_type (abstr_type bt_i bt_i) (abstr_type bt_i bt_i) in

  (* let ten = Abstr(Symbol "f", abstr_type bt_i bt_i, Abstr(Symbol "x", bt_i, Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Appl( Symbol "f",Symbol "x")))))))))))) in *)

  let ten = church_num(33) in

  let times = Abstr(Symbol "m", numeraltype, Abstr(Symbol "n", numeraltype, Abstr(Symbol "f", (abstr_type bt_i bt_i), Abstr(Symbol "x", bt_i,
    Appl(Appl(Symbol "m", Appl(Symbol "n", Symbol "f")),Symbol "x" ))))) in

  let thewhole = Appl(Appl(times,Appl(Appl(times,ten),ten)),ten) in




  print_string ("adding term zero: "^(Term.to_string thewhole)^"\n");
  let id_thewhole = create ts thewhole in
  print_string ("->index: "^(string_of_int id_thewhole)^"\n\n");

  let ten = church_num(32) in
  let thewhole = Appl(Appl(times,Appl(Appl(times,ten),ten)),ten) in

  print_string ("adding term zero: "^(Term.to_string thewhole)^"\n");
  let id_thewhole = create ts thewhole in
  print_string ("->index: "^(string_of_int id_thewhole)^"\n\n")
  (*print_string ("retrieve("^(string_of_int id_thewhole)^"): "^(Term.to_string (retrieve ts id_thewhole))^"\n")*)



let main =
try
 (* test1 ();
  test2 ();
  test3 ();
  test4 ();*)
  test5();
with
 | Failure x -> (prerr_string ("\nError found: \n" ^ x ^ "\n"); exit(255))
 | e -> (prerr_string ("\n" ^ Printexc.to_string e ^ "\n"); exit (255))
