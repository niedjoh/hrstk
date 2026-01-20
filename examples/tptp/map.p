% map function on lists
% source: Fuhs & Kop RTA 2012

thf(a_type,type,
    a: $tType ).

thf(b_type,type,
    b: $tType ).

thf(nil_type,type,
    nil: b ).

thf(cons_type,type,
    cons: a > b > b ).

thf(map_type,type,
    map: (a > a) > b > b ).

thf(map_base,axiom,
    ! [F: a>a] :
      ( map @ F @ nil
      = nil ) ).

thf(map_rec,axiom,
    ! [F: a>a, H: a, T : b] :
      ( map @ F @ (cons @ H @ T)
      = cons @ (F @ H) @ (map @ F @ T) ) ).
