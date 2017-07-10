
{
	open Lexing
  open Htparser
  exception Eof

  let incr_lineno lexbuf i =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + i;
      pos_bol = pos.pos_cnum;
    }

  (* HACK: newlines are not explicit in multiline comments,
   * so we need to count them. Otherwise any multiline comment
   * counts a one line, which gives wrong line numbers in the
   * parser's error reporting. *)
  open String
  let count_newlines str =
  	let idx i = try (index_from str i '\n') with Not_found -> -1 in
  	let lindex = ref 0 in
  	let count = ref 0 in
  	while (idx !lindex) >= 0 do
  		count := !count + 1;
  		lindex := idx !lindex + 1
  	done;
  	!count
(* Old type variables:
  let single_uote = ['\'']
  let sq_upper_word =           (single_quote)(upper_word)
*)
}


let digit =                   ['0'-'9']
let lower =                   ['a'-'z']
let upper =                   ['A'-'Z']
let alphanum =                ((lower)|(upper)|(digit)|['_'])
let any_char =                (_|'\n')
let ddollar =                 ['$']['$']
let unsigned_integer =        (digit)(digit)*
let signed_integer =          ['+''-'](unsigned_integer)
let decimal_part =            ['.'](digit)(digit)*
let real =                    ((signed_integer)|(unsigned_integer))(decimal_part)
let upper_word =              (upper)(alphanum)*

let sq_char =                 (['\032'-'\038''\040'-'\091''\093'-'\126']|['\\']['\'''\\'])
let single_quoted =           ['\''](sq_char)(sq_char)*['\'']

let lower_word =              (lower)(alphanum)*
let atomic_system_word =      (ddollar)(lower)(alphanum)*
let system_comment_one =      ['%'][' ']*(ddollar)(_)*
let system_comment_multi =    ['/']['*'][' ']*(ddollar)([^'*']*['*']['*']*[^'/''*'])*[^'*']*['*']['*']*['/']
let system_comment =          (system_comment_one)|(system_comment_multi)
let comment_one =             ['%'][^'\n']*
let comment_multi =           ['/']['*']([^'*']*['*']['*']*[^'/''*'])*[^'*']*['*']['*']*['/']
let comment =                 (comment_one)|(comment_multi)

rule token = parse
  | '&'    { AMPERSAND }
  | '@'    { AT_SIGN }
  | '^'    { CARET }
  | "cnf"  { CNF }
  | ':'    { COLON }
  | ','    { COMMA }
  | '='    { EQUALS }
  | "!!"   { DOUBLEEXCLAMATION }
  | '!'    { EXCLAMATION }
  | "fof"  { FOF }
  | "qmf"  { QMF }
  | ":="   { GETS }
  | '>'    { GREATER }
  | "hof"  { HOF }
  (* hope that's it: *)
  | "thf"  { HOF }

  | "$thf" { DTHF }
  | "$fof" { DFOF }
  | "$cnf" { DCNF }
  | "$fot" { DFOT }

  | "<="   { IF }
  | "<=>"  { IFF }
  | "=>"   { IMPLIES }
  | "include" { INCLUDE_TOK }
  | "input_clause"    { INPUT_CLAUSE }
  | "input_formula"    { INPUT_FORMULA }
  | "lambda"    { LAMBDA }
  | '['    { LBRKT }
  | '('    { LPAREN }
  | "->"    { MAP_TO }
  | "--"    { MMINUS }
  | "~&"    { NAMPERSAND }
  | "!="    { NEQUALS }
  | "<~>"    { NIFF }
  | "~|"    { NVLINE }
  | '.'    { PERIOD }
  | "++"    { PPLUS }
  | "??"   { DOUBLEQUESTION }
  | '?'    { QUESTION }
  | ']'    { RBRKT }
  | ')'    { RPAREN }
  | '~'    { TILDE }
  | "#box" { BOX }
  | "#dia" { DIAMOND }
  | "$false"    { TOK_FALSE }
  | "$i"    { TOK_I }
  | "$o"    { TOK_O }
  | "$int"    { TOK_INT }
  | "$real"    { TOK_REAL }
  | "$true"    { TOK_TRUE }
  | "$tType"    { TOK_TYPE }
  | '|'    { VLINE }

  | real as str     { Real str }
  | signed_integer as str   { Signed_integer str }
  | unsigned_integer as str { Unsigned_integer str }
  | decimal_part as str      { Decimal_part  str }

  (* | sq_upper_word as str { Sq_upper_word(str) } *)
  | single_quoted as str    { Single_quoted str }
  | upper_word as str      { Upper_word(str) }
  | lower_word as str     { Lower_word(str) }
  | atomic_system_word as str     { Atomic_system_word(str) }
  | comment as str  { incr_lineno lexbuf (count_newlines str); token lexbuf }
  | ['\n'] { incr_lineno lexbuf 1; token lexbuf }
  | [' ' '\t']    { token lexbuf }
  | ['\000'-'\040']|['\177']    { token lexbuf }
  | ['\041'-'\176']    { token lexbuf }
  | eof { EOF }

