% untyped lamda calculus
% source: Mayr & Nipkow TCS 1998

thf(t_type,type,
    t: $tType ).

thf(abs_type,type,
    abs: (t > t) > t ).

thf(app_type,type,
    app: t > t > t ).

thf(beta,axiom,
    ! [F: t>t, S: t] :
      ( app @ (abs @ (^ [X: t] : F @ X)) @ S
      = F @ S ) ) .

thf(eta,axiom,
    ! [S : t] :
      ( abs @ (^ [X: t] : app @ S @ X)
      = S ) ).
