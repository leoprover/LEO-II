(* ========================================================================= *)
(* A computability path order for LEO-II's terms                             *)
(* ========================================================================= *)

(** The computability path order of Niederhauser and Middeldorp, adapted to
    LEO-II's named-binder terms.

    The order is a higher-order generalisation of the recursive path orders
    familiar from first-order superposition.  It is well founded and stable
    under substitution, which are the two properties an orientation order
    needs, and it is decided pairwise: given two terms it answers whether one
    is greater, and it is allowed to answer neither.

    Two cautions, both of them properties of the order rather than of this
    implementation.

    - The order is not known to be transitive.  It may therefore be used to
      decide the orientation of one pair at a time, and must never be handed
      to a sorting function or used to build a total order over a set.  That
      is why this module offers [gt] and [compare] but no [sort].
    - [accessible] and [basic] of the published definition are fixed here at
      their trivially sound settings, under which the compatibility conditions
      hold vacuously.  The order is weaker for it, which is the right trade for
      a soundness-critical component.

    LEO-II keeps its terms in beta-normal but not eta-long form, so what is
    implemented is the beta-eta-normal order, not the beta-eta-long-normal
    variant that Nipkow-style rewriting calls for.

    @since 1.8.0 *)

type status = Lex | Mul

type verdict = Greater | Less | Equal | Incomparable

type params = {
  sort_prec : string -> int;
    (** rank of a base sort; a larger rank is the greater sort *)
  const_prec : string -> int;
    (** rank of a constant; equal ranks make the constants equivalent *)
  status : string -> status;
    (** how the arguments of equivalent heads are compared *)
  typing : string -> Hol_type.hol_type;
    (** the problem signature, for the companion order on types *)
  type_check : bool;
    (** whether a comparison must also respect the type order *)
}

val default_params : (string -> Hol_type.hol_type) -> params
(** A precedence that ranks constants by a stable hash of their names, all
    sorts equivalent, lexicographic status throughout, with the type check on.
    The hash makes the precedence total and well founded on symbols, so that
    equations between arbitrary distinct constants can be oriented, at the
    price of an arbitrary though run-stable choice of which way. *)

val type_gt : (string -> int) -> Hol_type.hol_type -> Hol_type.hol_type -> bool
(** The admissible type order: a function type dominates its own result type,
    and of two function types sharing an argument prefix the one with the
    greater result type is greater. *)

val type_ge : (string -> int) -> Hol_type.hol_type -> Hol_type.hol_type -> bool

val gt : params -> Term.term -> Term.term -> bool
(** The sound layer.  [gt p s t] holds when [s] is greater than [t] in the
    order.  It may be false in both directions for the same pair, and every
    caller must be prepared to do nothing in that case. *)

val compare : params -> Term.term -> Term.term -> verdict
(** Four-valued: the pair may be incomparable. *)

val gt_heuristic : params -> Term.term -> Term.term -> bool
(** The heuristic layer.  Falls back on a structural comparison when the order
    is undecided, so the answer is total but is not a reduction order.  Use it
    only to pick a canonical direction where any consistent choice will do.  It
    must never gate a rewrite. *)
