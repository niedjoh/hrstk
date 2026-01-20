% brouwer ordinals recursor
% source: Example 7.1 in Blanqui, Jouannaud & Rubio LMCS 2015

thf(o_type,type,
    o: $tType ).

thf(n_type,type,
    n: $tType ).

thf(a_type,type,
    a: $tType ).

thf(lim_type,type,
    lim: (n > o) > o ).

thf(zeroN,type,
    zeroN: n ).

thf(sucN,type,
    sucN: n > n ).

thf(zero,type,
    zero: o ).

thf(suc,type,
    suc: o > o ).

thf(rec,type,
    rec: o > a > (o > a > a) > ((n > o) > (n > a) > a) > a ).

thf(rec_zero,axiom,
    ! [U: a, V: o > a > a, W: (n > o) > (n > a) > a] :
      ( rec @ zero @ U @ V @ W
      = U ) ) .

thf(rec_suc,axiom,
    ! [X: o, U: a, V: o > a > a, W: (n > o) > (n > a) > a] :
      ( rec @ (suc @ X) @ U @ V @ W
      = V @ X @ (rec @ X @ U @ V @ W) ) ) .

thf(rec_base,axiom,
    ! [Y: n > o,U: a, V: o > a > a, W: (n > o) > (n > a) > a] :
      ( rec @ (lim @ Y) @ U @ V @ W
      = W @ Y @ (^ [N: n] : rec @ (Y @ N) @ U @ V @ W) ) ) .
