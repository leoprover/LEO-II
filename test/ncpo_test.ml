(* Checks of the term order against the worked examples of the thesis that
   introduced it (Tables 5.1, 5.3 and 5.4).  Build with:
     make -C src ncpo_test && ../test/ncpo_test *)
open Hol_type
open Term

let i = Basetype "i"
let o = Basetype "o"
let ii = Funtype (i, i)
let io = Funtype (i, o)

let sg = [("c", i); ("f", ii); ("g", ii); ("h", ii)]
let typing s = try List.assoc s sg with Not_found -> Basetype "'A"

let ranks = [("g", 3); ("h", 2); ("f", 2); ("c", 1)]
let p = { (Ncpo.default_params typing) with
          Ncpo.const_prec = (fun s -> try List.assoc s ranks with Not_found -> 0);
          Ncpo.sort_prec = (fun s -> if s = "o" then 1 else 0) }

let app f x = Appl (Symbol f, Symbol x)
let failures = ref 0

let check name expected actual =
  if expected = actual then Printf.printf "  ok    %-34s %b\n" name actual
  else begin
    incr failures;
    Printf.printf "  FAIL  %-34s expected %b, got %b\n" name expected actual
  end

let () =
  print_endline "type order (Table 5.1, with iota below o):";
  check "o > i" true (Ncpo.type_gt p.Ncpo.sort_prec o i);
  check "(i>o) > (i>i)" true (Ncpo.type_gt p.Ncpo.sort_prec io ii);
  check "i > o" false (Ncpo.type_gt p.Ncpo.sort_prec i o);
  check "(i>i) > i" true (Ncpo.type_gt p.Ncpo.sort_prec ii i);

  print_endline "accessible subterm (Table 5.3):";
  check "f(c) > c" true (Ncpo.gt p (app "f" "c") (Symbol "c"));
  check "c > f(c)" false (Ncpo.gt p (Symbol "c") (app "f" "c"));

  print_endline "precedence (Table 5.4, g > h > c):";
  check "g(c) > h(c)" true (Ncpo.gt p (app "g" "c") (app "h" "c"));
  check "h(c) > g(c)" false (Ncpo.gt p (app "h" "c") (app "g" "c"));

  print_endline "stability: never orient out of a variable head";
  check "X > c" false (Ncpo.gt p (Symbol "X") (Symbol "c"));
  check "f(c) > X" false (Ncpo.gt p (app "f" "c") (Symbol "X"));

  print_endline "irreflexive and four-valued";
  check "f(c) > f(c)" false (Ncpo.gt p (app "f" "c") (app "f" "c"));
  check "compare f(c) f(c) = Equal" true
    (Ncpo.compare p (app "f" "c") (app "f" "c") = Ncpo.Equal);
  check "compare X c = Incomparable" true
    (Ncpo.compare p (Symbol "X") (Symbol "c") = Ncpo.Incomparable);
  check "heuristic layer is total on that pair" true
    (Ncpo.gt_heuristic p (Symbol "X") (Symbol "c")
     <> Ncpo.gt_heuristic p (Symbol "c") (Symbol "X"));

  print_endline "abstraction: the body dominates";
  let lam = Abstr (Symbol "Y", i, app "f" "c") in
  check "(\\Y. f(c)) > c" true (Ncpo.gt p lam (Symbol "c"));

  if !failures = 0 then print_endline "\nall checks passed"
  else begin Printf.printf "\n%d check(s) failed\n" !failures; exit 1 end
