% replace negation by implication example
% source: Niederhauser & Middeldorp IWC 2025

thf(a_type,type,
    prop: $tType ).

thf (b_type,type,
     b: $tType ).

thf(bot_type,type,
    bot: prop ).

thf(top_type,type,
    top: prop ).

thf(neg_type,type,
    neg: prop > prop).

thf(and_type,type,
    and: prop > prop > prop ).

thf(or_type,type,
    or: prop > prop > prop ).

thf(impl_type,type,
    impl: prop > prop > prop ).

thf(repl_type,type,
    repl: (prop > prop) > prop > prop ).

thf(dneg,axiom,
    ! [X : prop] :
    ( neg @ Y
    = bot ) ).
