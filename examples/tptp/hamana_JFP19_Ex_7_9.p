% typed beta with protected variables
% source: Hamana JFP 2019

thf(a_type,type,
    a: $tType ).

thf(b_type,type,
    b: $tType ).

thf(bool_type,type,
    bool: $tType ).

thf(lam_type,type,
    lam: (a > b) > (a > b) ).

thf(app_type,type,
    app: (a > b) > a > b).

thf(var_type,type,
    var: a > a ).

thf(isvar_type,type,
    isvar: a > bool ).

thf(true_type,type,
    true: bool ).

thf(beta,axiom,
  ! [M : a>b, N : a] :
    ( app @ (lam @ (^ [X : a] : M @ (var @ X))) @ N
      = M @ N ) ).

thf(isvar,axiom,
    ! [X: a] :
      ( isvar @ (var @ X)
      = true ) ).
