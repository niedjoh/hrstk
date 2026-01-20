% breadth-first serach of labeled trees using continuations
% source: Example 5.2 in Blanqui, Jouannaud & Rubio LMCS 2015

thf(list_type,type,
    list: $tType ).

thf(con_type,type,
    con: $tType ).

thf(d_type,type,
    d: con ).

thf(c,type,
    c: ((con > list) > list) > con ).

thf(e_type,type,
    e: con > list ).

thf(e,axiom,
    ! [X: (con > list) > list] :
      ( e @ (c @ X)
      = X @ e ) ) .
