% artificial example showing strengh of neutralization.
% source: original

thf(a_type,type,
    a: $tType ).

thf(f_type,type,
    f: (a > a) > a > a ).

thf(g_type,type,
    g: a > a > a ).

thf(e,axiom,
    ! [Y: a, Z: a] :
      ( f @ (^ [X : a] : g @ X @ Y) @ Z
      = f @ (^ [X: a] : g @ Z @ Y) @ Z ) ).
