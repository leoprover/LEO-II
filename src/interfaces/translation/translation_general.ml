(* Constants and general definitions*)

open General
open Hol_type
open Term

type decoration_pred = hol_type -> bool

(*Generic translation error*)
exception TRANSLATION of string


(* Translation options *)

type translation =
    Simple | Kerber | FullyTyped | Experiment | ExperimentImproved
  | TFF_Experiment | FOF_Experiment | FOF_Full | FOF_Experiment_Erased
let print_translation = function
    Simple -> "simple"
  | Kerber -> "kerber"
  | FullyTyped -> "fully-typed"
  | Experiment -> "experiment"
  | ExperimentImproved -> "experiment_improved"
  | TFF_Experiment -> "tff_experiment"
  | FOF_Experiment -> "fof_experiment"
  | FOF_Full -> "fof_full"
  | FOF_Experiment_Erased -> "fof_experiment_erased"
let read_translation = function
    "simple" -> Simple
  | "kerber" -> Kerber
  | "fully-typed" -> FullyTyped
  | "experiment" -> Experiment
  | "experiment_improved" -> ExperimentImproved
  | "tff_experiment" -> TFF_Experiment
  | "fof_experiment" -> FOF_Experiment
  | "fof_full" -> FOF_Full
  | "fof_experiment_erased" -> FOF_Experiment_Erased
  | s -> raise (TRANSLATION ("Unknown translation:" ^ s))
(*"fo_translations" consists of the externally-available translations.
  "Simple" is only used internally, therefore it is excluded.*)
let fo_translations = [Kerber; FullyTyped; FOF_Experiment; TFF_Experiment; FOF_Full; FOF_Experiment_Erased]

type output_problem_format = TPTP_FOF | TPTP_TFF
(*FIXME here could add Guards and Kerber*)
type typing_device = Tags
(*FIXME could additionally specify mangling for certain encodings*)
type type_encoding =
    FullTypes of typing_device
  | PartTypes of typing_device
  | NativeTypes
  | NoTypes
type configuration = translation * (output_problem_format * type_encoding)
let configurations : configuration list =
   [(Experiment, (TPTP_FOF, FullTypes Tags));
    (ExperimentImproved, (TPTP_FOF, FullTypes Tags));
    (TFF_Experiment, (TPTP_TFF, NativeTypes));
    (FOF_Full, (TPTP_FOF, FullTypes Tags));
    (FOF_Experiment_Erased, (TPTP_FOF, NoTypes));
    (FOF_Experiment, (TPTP_FOF, PartTypes Tags))]


(* Constants *)

(** Translation constants  **)

let pK = "leoLit"
let tiK = "leoTi"
let appK = "leoAt"
let funtype_termK = "leoFt"
let special_symbols = [pK; tiK; appK; funtype_termK]

(*FIXME consts; see proxable image*)
let proxies = ["true"; "false"; "not"; "or"; "equals"; "forall"]

(*used to indicate that an equality needs to be lifted into
  a separate definition. "=" is changed temporarily into
  lift_marker_eq until the lifting is completed.*)
let lift_marker_eq = "=(lift)"

let proxy_boolK = "o"
let proxy_indK = "i"

let proxy_bool_ty = basetype proxy_boolK

(** Various prefixes used for type/const identifiers **)
let prefix_type = "t"
let prefix_const = "c"
(*prefix for lifted terms*)
let prefix_ll = "ll"
(*prefix for lifted formulas*)
let prefix_lf = "lf"


(** Name prefixes used for names of annotated formulas **)

let prefix_type_af = "type_"
let prefix_type_proxy_af = "typ_"
let prefix_type_lift_af = "tyl_"
let prefix_def_proxy_af = "prox_"


(** Logical constants **)

let leo2_iffK = Symbol Signature.iff
let leo2_eqK = Symbol Signature.equality
let leo2_forallK = Symbol Signature.forall


(** General definitions **)

(*appK-based term application*)
let ($@) t1 t2 = Symbol appK $ t1 $ t2

let is_variable s = Char.code s.[0] > 64 && Char.code s.[0] < 91
(*NOTE interpreted constants may also include extralogical symbols
       (but they currently don't)*)
(*"is_iconstant true" will include special_symbols*)
let is_iconstant nonstrict s =
  List.mem s (Signature.interpreted_constants @
                if nonstrict then special_symbols else [])
(*"is_uconstant true" will exclude special_symbols*)
let is_uconstant strict s = (*FIXME confusing, make is_uconstant and is_iconstant take similar arguments*)
  (Char.code s.[0] > 96 && Char.code s.[0] < 122) &&
    not (is_iconstant strict s)


(* Operations on Leo2's terms and types *)

(*Will subsequently be used for tagging*)
let rec type_to_term (ty : hol_type) = match ty with
    Basetype n ->
      let n' =
        if ty = Signature.bt_i then proxy_indK
        else if ty = Signature.bt_o then proxy_boolK
        (*type variables were probably put there by us*)
        else if is_variable n then n
        else if Hol_type.is_polyvar ty then remove_prefix "1" n
        else prefix_type ^ n
      in Symbol n'
  | Funtype (ty1, ty2) ->
      (Symbol funtype_termK $ type_to_term ty1) $ type_to_term ty2

let rec term_to_type (t : term) = match t with
  | Symbol n ->
      if n = proxy_indK then Signature.bt_i
      else if n = proxy_boolK then Signature.bt_o
      else if is_prefixed_with prefix_type n then
        Basetype (remove_prefix prefix_type n)
      else raise (TERM ("Term cannot be interpreted as base type", t))
  | Appl (Appl (t1, t2), t3) ->
      if t1 = Symbol funtype_termK then
        term_to_type t2 @-> term_to_type t3
      else raise (TERM ("Term cannot be interpreted as function type", t))
  | _ -> raise (TERM ("Term cannot be interpreted as function type", t))


(* Roles, based on TPTP *)

type af_role =
    Axiom | Plain | Conjecture | Type
  | Proxy (*Currently it's assumed that proxy (but not lifted) axioms contains
            required type info hardcoded, but this may be changed later. In any
            case, it may be useful to distinguish proxy formulas by role*)
let role_to_string = function
    Axiom -> "axiom"
  | Plain -> "plain"
  | Conjecture -> "conjecture"
  | Type -> "type"
  | _ -> failwith "Unprintable role" (*we don't want Proxy to be printed in FO output: use "plain" instead*)

let change_proxy_role_to_axiom (role : af_role) : af_role =
  match role with
      Proxy -> Axiom
    | _ -> role
