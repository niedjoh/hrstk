% classic DHP unif example

thf(a_type,type,
    a: $tType ).

thf(f_type,type,
    f: a > a ).

thf(example,axiom,
    ! [M : a > a > a, N : a > a > a] :
      ( ^ [X : a, Y : a]: M @ (f @ X) @ (f @ Y)
      = ^ [X : a, Y : a]: f @ ( N @ Y @ X) ) ) .
