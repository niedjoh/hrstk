% prenex normal form
% source: van de Pols PhD thesis, page 73

thf(t_type,type,
    t: $tType ).

thf(f_type,type,
    f: $tType ).

thf(not_type,type,
    not: f > f ).

thf(and,type,
    and: f > f > f ).

thf(or_type,type,
    or: f > f > f ).

thf(forall_type,type,
    forall: (t > f) > f ).

thf(exists_type,type,
    exists: (t > f) > f ).

thf(and_forall_r,axiom,
    ! [P: f, Q: t>f] :
      ( and @ P @ (forall @ (^ [X: t] : Q @ X))
      = forall @ (^ [X: t] : and @ P @ (Q @ X)) ) ) .

thf(and_forall_l,axiom,
    ! [P: f, Q: t>f] :
      ( and @ (forall @ (^ [X: t] : Q @ X)) @ P
      = forall @ (^ [X: t] : and @ (Q @ X) @ P) ) ) .

thf(or_forall_r,axiom,
    ! [P: f, Q: t>f] :
      ( or @ P @ (forall @ (^ [X: t] : Q @ X))
      = forall @ (^ [X: t] : or @ P @ (Q @ X)) ) ) .

thf(or_forall_l,axiom,
    ! [P: f, Q: t>f] :
      ( or @ (forall @ (^ [X: t] : Q @ X)) @ P
      = forall @ (^ [X: t] : or @ (Q @ X) @ P) ) ) .

thf(and_exists_r,axiom,
    ! [P: f, Q: t>f] :
      ( and @ P @ (exists @ (^ [X: t] : Q @ X))
      = exists @ (^ [X: t] : and @ P @ (Q @ X)) ) ) .

thf(and_exists_l,axiom,
    ! [P: f, Q: t>f] :
      ( and @ (exists @ (^ [X: t] : Q @ X)) @ P
      = exists @ (^ [X: t] : and @ (Q @ X) @ P) ) ) .

thf(or_exists_r,axiom,
    ! [P: f, Q: t>f] :
      ( or @ P @ (exists @ (^ [X: t] : Q @ X))
      = exists @ (^ [X: t] : or @ P @ (Q @ X)) ) ) .

thf(or_exists_l,axiom,
    ! [P: f, Q: t>f] :
      ( or @ (exists @ (^ [X: t] : Q @ X)) @ P
      = exists @ (^ [X: t] : or @ (Q @ X) @ P) ) ) .

thf(not_forall,axiom,
    ! [Q: t>f] :
      ( not @ (forall @ (^ [X: t] : Q @ X))
      = exists @ (^ [X: t] : not @ (Q @ X)) ) ) .

thf(not_exists,axiom,
    ! [Q: t>f] :
      ( not @ (exists @ (^ [X: t] : Q @ X))
      = forall @ (^ [X: t] : not @ (Q @ X)) ) ) .

