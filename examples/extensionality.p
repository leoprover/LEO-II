%------------------------------------------------------------------------------
% A first example.  Two predicates that agree everywhere are the same
% predicate.  This needs functional and Boolean extensionality, which is what
% LEO-II is for; it is not provable by first-order means alone.
%------------------------------------------------------------------------------
thf(p_type, type, p: $i > $o).
thf(q_type, type, q: $i > $o).

thf(agree, conjecture,
    ( ( ! [X: $i] : ( ( p @ X ) <=> ( q @ X ) ) )
   => ( p = q ) )).
%------------------------------------------------------------------------------
