%------------------------------------------------------------------------------
% A second example, with sets written as predicates: union distributes over
% intersection.  Quantification is over sets, so the problem is higher-order.
%------------------------------------------------------------------------------
thf(union_type, type, union: ( $i > $o ) > ( $i > $o ) > $i > $o).
thf(union_def, definition,
    ( union
    = ( ^ [A: $i > $o, B: $i > $o, X: $i] : ( ( A @ X ) | ( B @ X ) ) ) )).

thf(inter_type, type, inter: ( $i > $o ) > ( $i > $o ) > $i > $o).
thf(inter_def, definition,
    ( inter
    = ( ^ [A: $i > $o, B: $i > $o, X: $i] : ( ( A @ X ) & ( B @ X ) ) ) )).

thf(distributes, conjecture,
    ( ! [A: $i > $o, B: $i > $o, C: $i > $o] :
        ( ( union @ A @ ( inter @ B @ C ) )
        = ( inter @ ( union @ A @ B ) @ ( union @ A @ C ) ) ) )).
%------------------------------------------------------------------------------
