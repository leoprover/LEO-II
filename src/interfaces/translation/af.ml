(* Annotated formulas, based on TPTP *)

open General
open Translation_general
open App_term
open Translation_printing


type af =
    Formula of string * af_role * app_term
  | Typing (*FIXME don't use strings*) of string * string * string

let print_af cfg af =
  match af with
      Formula (name, af_role, ta) -> print_af_term cfg af_role name ta
    | Typing (name, symbol, ty_s) -> print_af_typing cfg name symbol ty_s

let transform_fmla_af pred f af =
  match af with
      Formula (name, af_role, ta) when pred af_role -> Formula (name, af_role, f ta)
    | _ -> af

(*project out the app_term values from af values*)
let (get_af_formulas : (af_role -> bool) -> af list -> app_term list) pred =
  let get_af_formula af =
    match af with
        Formula (_, af_role, ta) when pred af_role -> [ta]
      | _ -> []
  in
    List.map get_af_formula
    @> List.concat
