% surjective disjoint union
% source: van de Pols PhD thesis, page 74

thf(a_type,type,
    a: $tType ).

thf(b_type,type,
    b: $tType ).

thf(i_type,type,
    i: $tType ).

thf(u_type,type,
    u: $tType ).

thf(case,type,
    case: u > (a>i) > (b>i) > i ).

thf(inl,type,
    inl: a > u ).

thf(inr,type,
    inr: b > u ).

thf(case_l,axiom,
    ! [F: a>i, G: b>i, X: a] :
      ( case @ (inl @ X) @ F @ G
      = F @ X ) ) .

thf(case_r,axiom,
    ! [F: a>i, G: b>i, Y: b] :
      ( case @ (inr @ Y) @ F @ G
      = G @ Y ) ) .

thf(case_sym,axiom,
    ! [H: u>i, Z: u] :
      ( case @ Z @ (^ [X: a] : H @ (inl @ X)) @ (^ [Y: b] : H @ (inr @ Y))
      = H @ Z ) ) .
