(* Some general definitions,
   Some of these could be moved within specific modules (e.g. Hol_type)
*)

open Hol_type
open Term

let (|>) x f = f x
let (@>) f1 f2 x = f2 (f1 x)
let apfst f (x, y) = (f x, y)
let apsnd f (x, y) = (x, f y)
let ($) t1 t2 = Appl (t1, t2)
let (@->) ty1 ty2 = Funtype (ty1, ty2)
let curry f (x1, x2) = f x1 x2
let (~+) f x = (x, f x)
let default y f x = try f x with _ -> y
exception NO_SOME
let the x = match x with Some y -> y | None -> raise NO_SOME
let eq x y = x = y
let rec list_subtract l1 l2 = (*FIXME naive*)
  match (l1, l2) with
      ([], _) -> []
    | (_, []) -> l1
    | (x :: xs, y :: ys) ->
        if x = y then list_subtract xs l2
        else list_subtract [x] ys @ list_subtract xs l2
let (?!) b f x = if b then f x else x
let (?!?) b f x = if b x then f x else x

(*Tail-recursive combination of map with fold, where g and g'
  are discriminators on the result of applying f to an element
  of the list*)
let map_fold f g g' x l =
  let rec map_fold' l (l', x) =
    match l with
        [] -> (l', x)
      | z :: zs ->
          let result = f z
          in map_fold' zs (g result :: l', g' result x)
  in
    map_fold' l ([], x)
    |> apfst List.rev

let list_split_at n l =
  let rec list_split_at' n l left =
    if n = 0 then (left, l)
    else if l = [] then raise (Failure "list_split_at")
    else
      list_split_at' (n - 1) (List.tl l) (List.hd l :: left)
  in
    list_split_at' n l []
    |> apfst List.rev

let is_prefixed_with p s = String.sub s 0 (String.length p) = p
(*removes a prefix of length of p from s -- doesn't check if the
  removed prefix in fact matches p*)
let remove_prefix p s =
  let length_p = String.length p
  in String.sub s length_p (String.length s - length_p)

let dest_type ty =
  let rec dest_type' ty ty_l =
    match ty with
        Basetype _ -> (ty_l, ty)
      | Funtype (ty1, ty2) ->
          dest_type' ty2 (ty1 :: ty_l)
  in
    dest_type' ty []
    |> apfst List.rev


(*Term and type-related definitions*)

exception TERM of string * Term.term
exception TYPE of string * Hol_type.hol_type

(*This type is used whenever type information is irrelevant*)
let dummy_type = basetype "_"

let mk_false = Symbol Signature.cfalse
let mk_true = Symbol Signature.ctrue
let mk_not t = Symbol Signature.neg $ t
let mk_iff t1 t2 = Symbol Signature.iff $ t1 $ t2
let mk_if t1 t2 = Symbol Signature.implies $ t1 $ t2
let mk_all = (*FIXME reverse vars*)
  List.fold_right
    (function (v, ty) -> function t ->
       Symbol Signature.forall $ Abstr (Symbol v, ty, t))
let mk_or t1 t2 = Symbol Signature.disjunction $ t1 $ t2
let rec mk_app_from_list t = function
    [] -> t
  | (t' :: t's) -> mk_app_from_list (t $ t') t's

let dest_Symbol t =
  match t with
      Symbol n -> n
    | Appl _
    | Abstr _ ->
        raise (TERM ("dest_Symbol applied to non-Symbol", t))

(*e.g. match_type ('A -> $o) ($i -> $o) gives [('A, $i)]
       -- as would match_type ($i -> $o) ('A -> $o)*)
(*NOTE returns well-formed map*)
let match_type ?(acc = []) ty1 ty2 =
  let complain ty1 ty2 =
    TYPE ("Type mismatch with " ^
            Hol_type.to_string ty1,
          ty2) in
  let rec match_type' ty1 ty2 acc =
    match (ty1, ty2) with
        (Basetype s1, _)
      | (_, Basetype s1) ->
          let process_polyvar polyvar_ty other_ty =
            let s1 = dest_basetype polyvar_ty in
            let s1_in_acc = List.mem_assoc s1 acc
            in
              if s1_in_acc then
                let s1_ty = List.assoc s1 acc
                in
                  if s1_ty = other_ty then acc
                  else if Hol_type.is_polyvar s1_ty then
                    (s1, other_ty) :: (List.remove_assoc s1 acc)
                else
                  raise (TYPE ("Type variable mapped to both " ^
                                 Hol_type.to_string other_ty ^ " and " ^
                                 Hol_type.to_string s1_ty,
                               polyvar_ty))
              else
                if Hol_type.is_polyvar other_ty then acc
                else (s1, other_ty) :: acc
          in
            if Hol_type.is_polyvar ty1 then process_polyvar ty1 ty2
            else if Hol_type.is_polyvar ty2 then process_polyvar ty2 ty1
            else
              begin
                (*if ty1 ground then should be identical to ty2*)
                try
                  if dest_basetype ty2 = s1 then acc
                  else raise (complain ty1 ty2)
                with
                    Failure "dest_basetype" ->
                      (*ty2 must have been a Funtype*)
                      raise (complain ty1 ty2)
              end
      | (Funtype (ty1a, ty1b), Funtype (ty2a, ty2b)) ->
          match_type' ty1a ty2a acc
          |> match_type' ty1b ty2b
  in match_type' ty1 ty2 acc

(*e.g. inst_type ('A -> $o) [('A, $i)] gives ($i -> $o)*)
(*NOTE Assumes that "m" is well-formed*)
let rec inst_type m ty =
  match ty with
      Basetype s ->
        if List.mem_assoc s m then
          List.assoc s m
        else ty
    | Funtype (tya, tyb) ->
        Funtype (inst_type m tya, inst_type m tyb)

(*Simulates the application of a value of one type
  to a value of another type, returning the result type.
  i.e. given types A -> B and A, returns B.
  Also works with polymorphic types*)
(*NOTE similar to Hol_type.appl_type, but that function's
        assert was failing since it doesn't support
        matching*)
let type_apply ty1 ty2 =
  let complain () =
    TYPE ("Cannot apply function type to " ^
            Hol_type.to_string ty2,
          ty1)
  in
    match ty1 with
        Funtype (pre_ty1a, _) ->
          let m = match_type pre_ty1a ty2 in
          let (ty1a, ty1b) =
            match inst_type m ty1 with
                Funtype (ty1a, ty1b) -> (ty1a, ty1b)
              | _ -> raise (TYPE ("Expected function type", inst_type m ty1)) in
          let ty2' = inst_type m ty2
          in
            if ty1a = ty2' then
              (ty1b, m)
            else
              let m = match_type ty2 pre_ty1a in
              let (ty1a, ty1b) =
                match inst_type m ty1 with
                    Funtype (ty1a, ty1b) -> (ty1a, ty1b)
                  | _ -> raise (TYPE ("Expected function type", inst_type m ty1)) in
              let ty2' = inst_type m ty2
              in
                if ty1a = ty2' then
                  (ty1b, m)
                else
                  raise (complain ())
      | _ ->
          raise (complain ())
