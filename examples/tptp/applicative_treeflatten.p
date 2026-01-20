% applicative treeflatten
% source: Applicative_05__TreeFlatten in TPDB (Example 8.19 in Blanqui, Jouannaud & Rubio LMCS 2015)

thf(a_type,type,
    a: $tType ).

thf(nil_type,type,
    nil: a ).

thf(flatten_type,type,
    flatten: a > a ).

thf(concat_type,type,
    concat: a > a ).

thf(cons_type,type,
    cons: a > a > a ).

thf(append_type,type,
    append: a > a > a ).

thf(node_type,type,
    node: a > a > a ).

thf(map_type,type,
    map: (a > a) > a > a ).

thf(map_base,axiom,
    ! [F: a>a] :
      ( map @ F @ nil
      = nil ) ) .

thf(map_rec,axiom,
    ! [F: a>a, X: a, V: a] :
      ( map @ F @ (cons @ X @ V)
      = cons @ (F @ X) @ (map @ F @ V) ) ) .

thf(flatten,axiom,
    ! [X: a, V: a] :
      ( flatten @ (node @ X @ V)
      = cons @ X @ (concat @ (map @ flatten @ V)) ) ) .

thf(concat_base,axiom,
      ( concat @ nil
      = nil ) ) .

thf(concat_rec,axiom,
    ! [X: a, V: a] :
      ( concat @ (cons @ X @ V)
      = append @ X @ (concat @ V) ) ) .

thf(append_base,axiom,
    ! [V: a] :
      ( append @ nil @ V
      = V ) ) .

thf(append_rec,axiom,
    ! [X: a, U: a, V: a] :
      ( append @ (cons @ X @ U) @ V
      = cons @ X @ (append @ U @ V) ) ) .

