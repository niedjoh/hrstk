% differentiation
% source: extension of Example 3.4 in Jouannaud & Rubio ACM Trans. Com. Log. 2015

thf(real_type,type,
    real: $tType ).

thf(zero,type,
    zero: real ).

thf(one,type,
    one: real ).

thf(sin,type,
    sin: real > real ).

thf(cos,type,
    cos: real > real ).

thf(ln,type,
    ln: real > real ).

thf(diff,type,
    diff: (real > real) > real > real ).

thf(plus,type,
    plus: (real > real) > (real > real) > real > real ).

thf(minus,type,
    minus: (real > real) > real > real ).

thf(times,type,
    times: (real > real) > (real > real) > real > real ).

thf(div,type,
    div: (real > real) > (real > real) > real > real ).

thf(diff_const,axiom,
    ! [X : real, Y : real] :
      ( diff @ (^ [Z: real] : Y) @ X
      = zero) ).

thf(diff_id,axiom,
    ! [X : real] :
    ( diff @ (^ [Z: real] : Z) @ X
    = one ) ).

thf(diff_sin,axiom,
    ! [X : real, F : real > real] :
      ( diff @ (^ [Z : real] : sin @ (F @ Z)) @ X
      = times @ (^ [Z : real] : cos @ (F @ Z)) @ (diff @ (^ [Z : real] : F @ Z)) @ X ) ) .

thf(diff_cos,axiom,
    ! [X : real, F : real > real] :
      ( diff @ (^ [Z : real] : cos @ (F @ Z)) @ X
      = times @ (minus @ (^ [Z : real] : sin @ (F @ Z))) @ (diff @ (^ [Z : real] : F @ Z)) @ X) ) .

thf(diff_plus,axiom,
    ! [X : real, F : real > real, G : real > real] :
      ( diff @ (plus @ (^ [Z: real] : F @ Z) @ (^ [Z: real] : G @ Z)) @ X
      = plus @ (diff @ (^ [Z: real] : F @ Z)) @ (diff @ (^ [Z: real] : G @ Z)) @ X) ) .

thf(diff_times,axiom,
    ! [X : real, F: real > real, G: real > real] :
      ( diff @ (times @ (^ [Z : real] : F @ Z) @ (^ [Z : real] : G @ Z)) @ X
      = plus @ (times @ (diff @ (^ [Z : real] : F @ Z)) @ (^ [Z : real] : G @ Z))
             @ (times @ (^ [Z : real] : F @ Z) @ (diff @ (^ [Z : real] : G @ Z))) @ X ) ) .

thf(diff_ln,axiom,
    ! [X : real, F : real > real] :
      ( diff @ (^ [Z: real] : ln @ (F @ Z)) @ X
      = div @ (diff @ (^ [Z: real] : F @ Z)) @ F @ X ) ) .
