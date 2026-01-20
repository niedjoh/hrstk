% basic DPRS critical pair example
% source: Niederhauser & Middeldorp IWC 2025

thf(a_type,type,
    a: $tType ).

thf(c_type,type,
    c: (a > a) > a ).

thf(d_type,type,
    d: a ).

thf(f_type,type,
    f: a > a ).

thf(g_type,type,
    g: a > a ).

thf(h_type,type,
    h: a > a ).

thf(fg,axiom,
  ! [X : a] :
    ( f @ (g @ X)
      = f @ X ) ).

thf(c,axiom,
  ! [Z : a > a > a] :
    ( c @ (^ [Y	: a] : Z @ (g @ Y) @ (h @ Y))
      = Z @ d @ d ) ).
