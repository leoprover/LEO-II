(* Intermediate representation for terms, and related functions *)

open General
open Translation_general
open Hol_type
open Term

type app_term =
    Var of string * hol_type
  | Const of string * hol_type
  | App of app_term * app_term list
  | Abs of (string * hol_type) list * app_term
  | Quant of string * (string * hol_type) list * app_term

exception APP_TERM of string * app_term

(*appterm application*)
let ($$) ta1 tas = App (ta1, tas)
(*curried app_term application*)
let rec curried_app f xs =
  match xs with
      [] -> f
    | x :: xs -> curried_app (f $$ [x]) xs

let dest_App (ta : app_term) = match ta with
    App (t1, args) -> (t1, args)
  | Var _
  | Const _ -> (ta, [])
  | Abs _ -> raise (APP_TERM ("dest_App applied to Abs", ta))
  | Quant _ -> raise (APP_TERM ("dest_App applied to Quant", ta))
let dest_Var ta = match ta with
    Var (s, ty) -> (s, ty)
  | _ -> raise (APP_TERM ("dest_Var applied incorrectly", ta))
let is_Const ta = match ta with
    Const _ -> true
  | _ -> false
let dest_Const ta = match ta with
    Const (s, ty) -> (s, ty)
  | _ -> raise (APP_TERM ("dest_Const applied incorrectly", ta))
let dest_Quant ta = match ta with
    Quant (qrtf, vars, ta') -> (qrtf, vars, ta')
  | _ -> raise (APP_TERM ("dest_Quant applied incorrectly", ta))

let rec type_of_appterm ta =
  match ta with
      Var (_, ty) -> ty
    | Const (_, ty) -> ty
    | App (ta1, tas) ->
        let infer_type () =
          let ta1_ty = type_of_appterm ta1 in
          let (ta1_ty_domains, result_type) = dest_type ta1_ty in
          let tas_tys = List.map type_of_appterm tas in
            begin
              try
                let (lf, rt) = list_split_at (List.length tas_tys) ta1_ty_domains in
                let m =
                  List.fold_right
                    (fun (lf1, tas_tys1) m' ->
                       match_type ~acc:m' lf1 tas_tys1)
                    (List.combine lf tas_tys)
                    []
                in
                  (*match type variables*)
                  if List.map (inst_type m) lf = List.map (inst_type m) tas_tys then
                    Hol_type.mk_funtype rt result_type
                    |> inst_type m (*instantiate type variables*)
                  else
                    raise (TYPE ("Type mismatch with arguments [" ^
                                   String.concat ", " (List.map Hol_type.to_string lf) ^ "]",
                                 ta1_ty))
              with
                  Failure "list_split_at" ->
                    raise (APP_TERM ("Type inference failed: too many arguments", ta))
            end
        in
          (*prefer using cached type, if available, rather than re-inferring*)
          if default false (dest_Const @> fst @> eq appK) ta1 ||
            default false (dest_Const @> fst @> eq tiK) ta1 then
              let ta1_ty = (dest_Const @> snd) ta1
              in
                if ta1_ty = dummy_type then
                  infer_type ()
                else ta1_ty
          else infer_type ()
    | Abs (vars, ta') ->
        Hol_type.mk_funtype (List.map snd vars) (type_of_appterm ta')
    | Quant (_, _, ta') ->
        (*Could omit this check to gain speed*)
        if type_of_appterm ta' = Signature.bt_o then
          Signature.bt_o
        else
          raise (APP_TERM ("Term does not have boolean type", ta'))

let freevars_of ta =
  let rec freevars_of' binds ta acc = match ta with
      Var (n, ty) ->
        begin
          (*bound variables aren't free*)
          try
            let ty' = List.assoc n binds
            in if ty = ty' then acc
              else raise (TYPE ("Mismatched type: expected" ^ Hol_type.to_string ty, ty'))
          with Not_found ->
            (*free variables are already free*)
            try
              let ty' = List.assoc n acc
              in if ty = ty' then acc
                else raise (TYPE ("Mismatched type: expected" ^ Hol_type.to_string ty, ty'))
            with Not_found -> (n, ty) :: acc
        end
    | Const _ -> acc
    | App (ta1, tas) ->
        List.fold_right
          (freevars_of' binds)
          tas
          (freevars_of' binds ta1 acc)
    | Abs (vars, ta')
    | Quant (_, vars, ta') ->
        freevars_of' (binds @ vars) ta' acc
  in freevars_of' [] ta []

(*Print out term in THF*)
let rec app_term_to_string ta =
  let string_vars vars =
    String.concat ", " (List.map (fun (s, ty) -> s ^ ":" ^ Hol_type.to_string ty) vars)
  in match ta with
      Var (s, _)
    | Const (s, _) -> s
    | App (Const ("=" as c, _), [t1; t2])
    | App (Const ("!=" as c, _), [t1; t2])
    | App (Const ("&" as c, _), [t1; t2])
    | App (Const ("<=>" as c, _), [t1; t2])
    | App (Const ("=>" as c, _), [t1; t2])
    | App (Const ("|" as c, _), [t1; t2]) ->
        "(" ^ app_term_to_string t1 ^ " " ^ c ^ " " ^ app_term_to_string t2 ^ ")"
    | App (ta, tas) ->
        app_term_to_string ta ^ "(" ^ String.concat ", " (List.map app_term_to_string tas) ^ ")"
    | Abs (vars, ta) ->
        "^[" ^ string_vars vars ^ "]:(" ^ app_term_to_string ta ^ ")"
    | Quant (s, vars, ta) ->
        s ^ "[" ^ string_vars vars ^ "]:(" ^ app_term_to_string ta ^ ")"

(*return term at the head of an application*)
let rec head_of ta = match ta with
    App (ta', _) -> head_of ta'
  | _ -> ta
(*modify the constant at the head of an application*)
let rec head_constname_to s ta = match ta with
    App (ta', tas) -> App (head_constname_to s ta', tas)
  | Const (_, ty) -> Const (s, ty)
  | _ -> raise (APP_TERM ("Head term is not a constant", ta))
let rec head_consttype_to ty ta = match ta with
    App (ta', tas) -> App (head_consttype_to ty ta', tas)
  | Const (s, _) -> Const (s, ty)
  | _ -> raise (APP_TERM ("Head term is not a constant", ta))
let rec head_atomtype_to ty ta = match ta with
    App (ta', tas) -> App (head_atomtype_to ty ta', tas)
  | Const (s, _) -> Const (s, ty)
  | Var (s, _) -> Var (s, ty)
  | _ -> raise (APP_TERM ("Head term is not a constant/variable", ta))
let mk_quant qtfr vars ta =
  if List.length vars = 0 then ta
  else Quant (qtfr, vars, ta)

(*navigate down a term, instantiating type variables*)
let rec inst_type_of_term m ta =
  let inst_type_of_typing m (s, ty) = (s, inst_type m ty)
  in
    match ta with
        Var (s, ty) -> Var (s, inst_type m ty)
      | Const (s, ty) ->
          if List.mem s special_symbols then ta
          else Const (s, inst_type m ty)
      | App (ta1, tas) -> App (inst_type_of_term m ta1, List.map (inst_type_of_term m) tas)
      | Abs (vars, ta) ->
          Abs (List.map (inst_type_of_typing m) vars,
               inst_type_of_term m ta)
      | Quant (s, vars, ta) ->
          Quant (s, List.map (inst_type_of_typing m) vars,
                 inst_type_of_term m ta)

(*FIXME can also include interpreted symbols into the intermediate
  language (e.g. And for "&", etc)*)
(*Handle the THF !-combinator in our intermediate language*)
let rec mark_quantifiers (ta : app_term) : app_term = match ta with
    Var _ -> ta
  | Const _ -> ta
  | (*!-quantification*)
    App (Const ("!"(*FIXME const*), _), [Abs ([(x, ty)], t')]) ->
      let rest = mark_quantifiers t' in
        begin
          match rest with
              Quant (qtfr, vars, t') ->
                if qtfr = Signature.forall
                then Quant (qtfr, (x, ty) :: vars, t')
                else Quant (Signature.forall, [(x, ty)], rest)
            | _ -> Quant (Signature.forall, [(x, ty)], rest)
        end
  | App (t, ts) -> App (mark_quantifiers t, List.map mark_quantifiers ts)
  | Abs (vars, t') -> Abs (vars, mark_quantifiers t')
  | Quant _ -> raise (APP_TERM ("Quant should not appear in arguments", ta))


(* Less general definitions (since they mention constants
   defined in Translation_general) *)

(*appK-based appterm application
  NOTE appK is not appropriately typed -- it is given the
       type of the applicative expression. The typing info
       of its arguments can be obtained by looking at
       the arguments themselves*)
let ($@@) ta1 ta2 =
  let ty1 = type_of_appterm ta1 in
  let ty2 = type_of_appterm ta2 in
  let (at_ty, _) = type_apply ty1 ty2
  in Const (appK, at_ty) $$ [ta1; ta2]

let from_leo2_const leo2K = Const (dest_Symbol leo2K, Termsystem.type_of (Termsystem.term2xterm leo2K))
let iffK = from_leo2_const leo2_iffK
let eqK = from_leo2_const leo2_eqK

let pK_ty = basetype proxy_boolK @-> Signature.bt_o
let pK_ta = Const (pK, pK_ty)
(*change result type of ta (i.e. $o) to its type proxy, then apply pK wrapping.
  this maintains well-typed terms*)
let mk_pK_app ta =
  let ty = type_of_appterm ta
  in
    if ty = Signature.bt_o  then
      (*FIXME horrible combinators*)
      let (args, _) =
        if (head_of @> is_Const) ta then
          (head_of @> dest_Const @> snd @> dest_type) ta
        else (*must be variable*)
          (head_of @> dest_Var @> snd @> dest_type) ta
      in
        pK_ta $$ [head_atomtype_to
                    (Hol_type.mk_funtype args (basetype proxy_boolK))
                    ta]
    else
      raise (APP_TERM ("Could not make pK: term is not Boolean result-typed (it has type " ^
                         Hol_type.to_string ty ^ ")",
                       ta))

(*FIXME make term_to_appterm work relative to each function's minimum
  arity*)
(*Translate one term representation into the other. All applications
  should have a constant/var/abstraction at their head. If no_types
  then Var and Const atoms contain dummy type info*)
let rec term_to_appterm ((tr, _)  as cfg : Translation_general.configuration) no_types
    (binds : (string * hol_type) list) (t : term) : app_term =
  match t with
      Symbol s ->
        (*variables and constants have a simple lexical distinction*)
        if Translation_general.is_variable s
        then Var (s,
                  if no_types then
                    dummy_type
                  else
                    List.assoc s binds)
        else Const (s,
                    (*exempt special_symbols from typing*)
                    if no_types || List.mem s special_symbols then dummy_type
                    else
                      let type_of_symbol s =
                        try
                          if tr = Experiment then
                            dummy_type
                          else
                            let s' =
                              (* Counter the renaming done by offset_constnames *)
                              if List.mem s (special_symbols @ proxies @ Signature.interpreted_constants) then s
                              else String.sub s 1 (String.length s - 1)
                            in Termsystem.type_of (Termsystem.term2xterm (Symbol s'))
                        with
                            e ->
                              (*TRANSLATION isn't caught further up, so we're guaranteed that
                                the exception is reported*)
                              raise (TRANSLATION (Printexc.to_string e))
                      in
                        if is_iconstant false s then
                          (*Interpreted symbols are typed by the signature*)
                          type_of_symbol s
                        else if List.mem s proxies then
                          (*proxies' types aren't currently used*)
                          dummy_type (*FIXME should type proxies*)
                        else
                          (*must be a constant: look in the signature*)
                          type_of_symbol s
                   )
    | Appl (Appl (Symbol "leoTi"(*FIXME const*) as t1, t2), t3) ->
        (*ignore encoded type information*)
        term_to_appterm cfg no_types binds t1 $$
          [term_to_appterm cfg no_types binds t2;
           term_to_appterm cfg true binds t3]
    | Appl (Appl (t1a, t1b), t2) ->
        let (t', args) = dest_App (term_to_appterm cfg no_types binds t1a) in
          t' $$ (args @
           [term_to_appterm cfg no_types binds t1b;
            term_to_appterm cfg no_types binds t2]) (*FIXME inefficient*)
    | Appl (t1, t2) ->
          term_to_appterm cfg no_types binds t1 $$ [term_to_appterm cfg no_types binds t2]
    | Abstr (Symbol n, ty, t') ->
        let rest = term_to_appterm cfg no_types ((n, ty) :: binds) t' in
          begin
            match rest with
                Abs (vars, t') -> Abs ((n, ty) :: vars, t')
              | _ ->
                  Abs ([(n, ty)], rest)
          end
    | Abstr (_, ty, t') ->
        raise (TERM ("term_to_appterm applied to nonsense Abstr", t))

let check_head_const is_curried pred ta =
  let maybe_head =
    if is_curried then head_of else (fun x -> x)
  in
    default false (maybe_head @> dest_Const @> fst @> pred) ta
