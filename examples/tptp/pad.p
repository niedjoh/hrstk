% process algebra with data
% source: van de Pols PhD thesis, page 75

thf(proc_type,type,
    proc: $tType ).

thf(data_type,type,
    data: $tType ).

thf(plus,type,
    plus: proc > proc > proc ).

thf(times,type,
    times: proc > proc > proc ).

thf(delta,type,
    delta: proc ).

thf(sigma,type,
    sigma: (data > proc) > proc ).

thf(a3,axiom,
    ! [X: proc] :
      ( plus @ X @ X
      = X ) ) .

thf(a4,axiom,
    ! [X: proc, Y: proc, Z: proc] :
      ( times @ (plus @ X @ Y) @ Z
      = plus @ (times @ X @ Z) @ (times @ Y @ Z) ) ) .

thf(a5,axiom,
    ! [X: proc, Y: proc, Z: proc] :
      ( times @ (times @ X @ Y) @ Z
      = times @ X @ (times @ Y @ Z) ) ) .

thf(a6,axiom,
    ! [X: proc] :
      ( plus @ X @ delta
      = X ) ) .

thf(a7,axiom,
    ! [X: proc] :
      ( times @ delta @ X
      = delta ) ) .

thf(sum1,axiom,
    ! [X: proc] :
      ( sigma @ (^ [D0 : data] : X)
      = X ) ) .

thf(sum3,axiom,
    ! [P: data > proc, D: data] :
      ( plus @ (sigma @ (^ [D0 : data] : P @ D0)) @ (P @ D)
      = sigma @ (^ [D0 : data] : P @ D0) ) ) .

thf(sum4,axiom,
    ! [P: data > proc, Q: data > proc] :
      ( sigma @ (^ [D0 : data] : plus @ (P @ D0) @ (Q @ D0))
      = plus @ (sigma @ (^ [D0 : data] : P @ D0)) @ (sigma @ (^ [D0 : data] : Q @ D0)) ) ) .

thf(sum5,axiom,
    ! [P: data > proc, X: proc] :
      ( times @ (sigma @ (^ [D0 : data] : P @ D0)) @ X
      = sigma @ (^ [D0 : data] : times @ (P @ D0) @ X) ) ) .

