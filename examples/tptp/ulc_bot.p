% untyped lambda calculus with error value bot
% source: Mayr & Nipkow TCS 1998

thf(t_type,type,
    t: $tType ).

thf(abs_type,type,
    abs: (t > t) > t ).

thf(app_type,type,
    app: t > t > t ).

thf(bot_type,type,
    bot: t ).

thf(beta,axiom,
    ! [F: t>t, S: t] :
      ( app @ (abs @ (^ [X: t] : F @ X)) @ S
      = F @ S ) ) .

thf(eta,axiom,
    ! [S : t] :
      ( abs @ (^ [X: t] : app @ S @ X)
      = S ) ).

thf(app_bot,axiom,
    ! [S: t] :
      ( app @ bot @ S
      = bot ) ) .

thf(abs_bot,axiom,
    ! [S: t] :
      ( abs @ (^ [X: t] : bot)
      = bot ) ) .
