% negational normal form
% source: Mayr & Nipkow TCS 1998

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

thf(not_not,axiom,
    ! [P: f] :
      ( not @ (not @ P)
      = P ) ) .

thf(not_and,axiom,
    ! [P: f, Q: f] :
      ( not @ (and @ P @ Q)
      = or @ (not @ P) @ (not @ Q) ) ) .

thf(not_or,axiom,
    ! [P: f, Q: f] :
      ( not @ (or @ P @ Q)
      = and @ (not @ P) @ (not @ Q) ) ) .

thf(not_forall,axiom,
    ! [R: t>f] :
      ( not @ (forall @ (^ [X: t]: R @ X))
      = exists @ (^ [X: t]: not @ (R @ X)) ) ) .

thf(not_exists,axiom,
    ! [R: t>f] :
      ( not @ (exists @ (^ [X: t]: R @ X))
      = forall @ (^ [X: t]: not @ (R @ X)) ) ) .
