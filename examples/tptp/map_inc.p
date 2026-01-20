% map with partially applied function
% source: subset of AotoYamada_05_014 in TPDB (Example 8.20 in Blanqui, Jouannaud & Rubio LMCS 2015)

thf(a_type,type,
    a: $tType ).

thf(b_type,type,
    b: $tType ).

thf(zero_type,type,
    zero: b ).

thf(nil_type,type,
    nil: a ).

thf(inc_type,type,
    inc: a > a ).

thf(s_type,type,
    s: b > b ).

thf(plus_type,type,
    plus: b > b > b ).

thf(map_type,type,
    map: (b > b) > a > a ).

thf(cons_type,type,
    cons: b > a > a ).

thf(plus_base,axiom,
    ! [X: b] :
      ( plus @ zero @ X
      = X ) ) .

thf(plus_rec,axiom,
    ! [X: b, Y: b] :
      ( plus @ (s @ Y) @ X
      = s @ (plus @ Y @ X) ) ) .

thf(map_base,axiom,
    ! [F: b>b] :
      ( map @ F @ nil
      = nil ) ) .

thf(map_rec,axiom,
    ! [F: b>b, U: b, V: a] :
      ( map @ F @ (cons @ U @ V)
      = cons @ (F @ U) @ (map @ F @ V) ) ) .

thf(inc,axiom,
    ! [V: a]:
      ( inc @ V
      = map @ (plus @ (s @ zero)) @ V ) ) .
