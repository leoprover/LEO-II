(* Collection of string-conversion functions *)

open General
open Translation_general
open App_term
open Hol_type


(* Type proxy conversions *)

(*Maps types to their proxies (in effect just works on $o)*)
let proxy_basetype_for s =
  if s = Hol_type.dest_basetype Signature.bt_o then proxy_boolK
  else if s = Hol_type.dest_basetype Signature.bt_i ||
    s = Hol_type.dest_basetype Signature.bt_type then s
  else if s.[0] = '\'' then s (*type variables*)
  else prefix_type ^ s


(* Printing *)

(*Creates well-formed tff type declarations.
  If do_proxy then creates type proxy for $o to allow for proxies
  for logical constants to be inserted in terms.
  I.e. if do_proxy=false then it just pretty-prints a type in TFF.
  NOTE $o should be proxies only where necessary, but currently it
       is proxied everywhere and pK is used to wrap $o-proxied
       constants (to simplify matters).
       Ideally should check if at_formula_level, and not proxy
       $o-valued constants which never appear at term level.
*)
type fo_type = string list * string
let tff_type_to_string do_proxy ty : string =
  (*Transform an FO type by inserting type proxies*)
  let proximate_fo_type (arg_ty_ss, result_ty_s) : fo_type =
      (List.map proxy_basetype_for arg_ty_ss,
       proxy_basetype_for result_ty_s) in
  (*uncurries the HOL function, if possible, to show
    list of argument types and the result type*)
  let rec uncurry ty ty_acc : fo_type =
    match ty with
        Basetype s -> (ty_acc, s)
      | Funtype (Basetype s, ty2) -> uncurry ty2 (s :: ty_acc)
      | Funtype (Funtype _, _) ->
          raise (TYPE ("Cannot convert high-type function into TFF", ty)) in
  let (args, result) =
    let uncurried_ty = uncurry ty []
    in if do_proxy then apfst List.rev (proximate_fo_type uncurried_ty) else uncurried_ty in
    if List.length args = 0 then
      result
    else if List.length args = 1 then
      List.hd args ^ " > " ^ result
    else
      "(" ^ String.concat " * " args ^ ")" ^ " > " ^ result


(*FIXME for each function symbol should have the minimum arity*)
let rec print_appterm ((tr, (fmt, _)) as cfg : Translation_general.configuration) (ta : app_term) : string = match tr with
    Experiment ->
      begin
        (*"Experiment" only works for TPTP_FOF*)
        match ta with
            Var (s, _)
          | Const (s, _) -> s
          (* FIXME incomplete? *)
          | App (Const ("=" as c, _), [t1; t2])
          | App (Const ("!=" as c, _), [t1; t2]) ->
              print_appterm cfg t1 ^ " " ^ c ^ " " ^ print_appterm cfg t2
          | App (Const ("&" as c, _), [t1; t2])
          | App (Const ("|" as c, _), [t1; t2]) ->
              "(" ^ print_appterm cfg t1 ^ " " ^ c ^ " " ^ print_appterm cfg t2 ^ ")"
          | Quant (quantifier, vars, t') ->
              quantifier ^ "[" ^
                String.concat "," (List.map fst vars) ^ "]: " ^
                "(" ^ print_appterm cfg t' ^ ")"
          | App (t, ts) ->
              (*FIXME emulating bracketing*)
              let head_is_negation = default false (dest_Const @> fst @> eq Signature.neg) t in
              (if head_is_negation then
                 "(" else "") ^
                print_appterm cfg t ^
                (*FIXME emulating old spacing*)
                if head_is_negation then
                  " " ^ print_appterm cfg (List.hd ts) ^ ")"
                else
                  if List.length ts = 0 then ""
                  else
                    "(" ^ String.concat "," (List.map (print_appterm cfg) ts) ^ ")"
          | Abs _ ->
              raise (APP_TERM ("Abstraction not supported in FOF", ta))
      end
  | FOF_Experiment
  | FOF_Full
  | FOF_Experiment_Erased
  | ExperimentImproved ->
      begin
        (*FIXME spacing in ", " added for readability*)
        match (fmt, ta) with
            (TPTP_FOF, Var (s, _))
          | (TPTP_FOF, Const (s, _)) -> s
          (* FIXME incomplete? *)
          | (TPTP_FOF, App (Const ("=" as c, _), [t1; t2]))
          | (TPTP_FOF, App (Const ("!=" as c, _), [t1; t2]))
          | (TPTP_FOF, App (Const ("&" as c, _), [t1; t2]))
          | (TPTP_FOF, App (Const ("<=>" as c, _), [t1; t2]))
          | (TPTP_FOF, App (Const ("=>" as c, _), [t1; t2]))
          | (TPTP_FOF, App (Const ("|" as c, _), [t1; t2])) ->
              "(" ^ print_appterm cfg t1 ^ " " ^ c ^ " " ^ print_appterm cfg t2 ^ ")"
          | (TPTP_FOF, Quant (quantifier, vars, t')) ->
              quantifier ^ "[" ^
                String.concat ", " (List.map fst vars) ^ "]: " ^
                "(" ^ print_appterm cfg t' ^ ")"
          | (TPTP_FOF, App (t, ts)) ->
                print_appterm cfg t ^
                  if List.length ts = 0 then ""
                  else
                    "(" ^ String.concat ", " (List.map (print_appterm cfg) ts) ^ ")"
          | (TPTP_FOF, Abs _) ->
              raise (APP_TERM ("Abstraction not supported in FOF", ta))
          | _ -> raise (TRANSLATION "Unimplemented")
      end
  | TFF_Experiment ->
      begin
        match ta with
            Var (s, _)
          | Const (s, _) -> s
          (* FIXME incomplete? e.g. need "<=>" and "=>"*)
          | App (Const ("=" as c, _), [t1; t2])
          | App (Const ("!=" as c, _), [t1; t2])
          | App (Const ("&" as c, _), [t1; t2])
          | App (Const ("<=>" as c, _), [t1; t2])
          | App (Const ("=>" as c, _), [t1; t2])
          | App (Const ("|" as c, _), [t1; t2]) ->
              "(" ^ print_appterm cfg t1 ^ " " ^ c ^ " " ^ print_appterm cfg t2 ^ ")"
          | Quant (quantifier, vars, t') ->
              let var_to_string (s, ty) = s ^ ":" ^ tff_type_to_string true ty in
                quantifier ^ "[" ^
                  String.concat ", " (List.map var_to_string vars) ^ "]: " ^
                  "(" ^ print_appterm cfg t' ^ ")"
          | App (t, ts) ->
                print_appterm cfg t ^
                  if List.length ts = 0 then ""
                  else
                    "(" ^ String.concat ", " (List.map (print_appterm cfg) ts) ^ ")"
          | Abs _ ->
              raise (APP_TERM ("Abstraction not supported in TFF", ta))
      end
  | _ -> raise (TRANSLATION "Unimplemented")

(*Generates strings encoding an annotated formula, in a TPTP language*)
let combine_af_string ((tr, _) : Translation_general.configuration) (af_role : af_role) name fmla_s =
  match tr with
      Experiment ->
        (*spacing emulates the "fully-typed" translation*)
        " fof(" ^ name ^ "," ^ Translation_general.role_to_string af_role ^ "," ^
          fmla_s ^ ").\n"
    | FOF_Experiment
    | FOF_Full
    | FOF_Experiment_Erased
    | ExperimentImproved ->
        (*NOTE there is a small difference in spacing compared to Experiment*)
        "fof(" ^ name ^ ", " ^ Translation_general.role_to_string af_role ^ ", " ^
          fmla_s ^ ").\n"
    | TFF_Experiment ->
        "tff(" ^ name ^ ", " ^ Translation_general.role_to_string af_role ^ ", " ^
          fmla_s ^ ").\n"
    | _ -> raise (TRANSLATION "Unimplemented")

let print_af_term cfg af_role name t =
  let t_s =
    let (pref, suff) =
      match t with
          App (Const (_, _) as c, _) ->
            if c = pK_ta then ("(", ")") else ("", "")
        | _ -> ("", "")
    in pref ^ print_appterm cfg ((* to_cnf *) t) ^ suff
  in combine_af_string cfg (change_proxy_role_to_axiom af_role) name t_s

let print_af_typing ((tr, _) as cfg) name symbol ty_s =
  match tr with
      TFF_Experiment -> combine_af_string cfg Type name (symbol ^ ": " ^ ty_s)
    | _ -> raise (TRANSLATION "Translation doesn't support typing")
