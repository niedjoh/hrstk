% replace negation by implication example
% source: Niederhauser & Middeldorp IWC 2025

thf(a_type,type,
    prop: $tType ).

thf(bot_type,type,
    bot: prop ).

thf(top_type,type,
    top: prop ).

thf(neg_type,type,
    neg: prop > prop ).

thf(and_type,type,
    and: prop > prop > prop ).

thf(or_type,type,
    or: prop > prop > prop ).

thf(impl_type,type,
    impl: prop > prop > prop ).

thf(repl_type,type,
    repl: (prop > prop) > prop > prop ).

thf(repl1,axiom,
  ! [F : prop > prop, X : prop] :
    ( repl @ (^ [Y : prop] : F @ (neg @ Y)) @ X
      = F @ (impl @ X @ bot) ) ).

thf(repl2,axiom,
  ! [F : prop > prop, X : prop] :
    ( repl @ (^ [Y : prop] : F @ Y) @ X
      = F @ X ) ).

thf(dneg,axiom,
    ! [X : prop] :
    ( neg @ (neg @ X)
      = X ) ).

thf(negToImpl,axiom,
    ! [X : prop] :
    ( neg @ X
      = impl @ X @ bot ) ).

thf(negImplCancel,axiom,
    ! [X : prop] :
    ( neg @ (impl @ X @ bot)
      = X ) ).

thf(dimpl,axiom,
    ! [X : prop] :
    ( impl @ (impl @ X @ bot) @ bot 
      = X ) ).
