% basic DPRS critical pair example
% source: Niederhauser & Middeldorp IWC 2025

thf(a_type,type,
    a: $tType ).

thf(b_type,type,
    b: $tType ).

thf(c_type,type,
    c: (a > a) > a ).

thf(d_type,type,
    d: a ).

thf(e_type,type,
    e: b > a ).

thf(f_type,type,
    f: a > a ).

thf(g_type,type,
    g: a > a ).

thf(h_type,type,
    h: a > b ).

thf(fg,axiom,
  ! [X : a] :
    ( f @ (g @ X)
      = f @ X ) ).

thf(hg,axiom,
  ! [X : a] :
    ( h @ (g @ X)
      = h @ X ) ).

thf(c,axiom,
  ! [Z : a > a] :
    ( c @ (^ [Y	: a] : Z @ ( g @ Y))
      = Z @ d ) ).
