% artificial example showing strengh of neutralization.
% source: original

thf(a_type,type,
    a: $tType ).

thf(fNew_type,type,
    fNew: a > a > a ).

thf(g_type,type,
    g: a > a > a ).

thf(botAA_type,type,
    botAA: a > a ).

thf(e,axiom,
    ! [Y: a, Z: a] :
      ( fNew @ (g @ (botAA @ Z) @ Y) @ Z
      = fNew @ (g @ Z @ Y) @ Z ) ).
