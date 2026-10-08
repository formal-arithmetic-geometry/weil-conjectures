+++
id = "lemma-constructible-pullback-locally-constant"
kind = "lemma"
title = "Pullback of locally constant sheaves"
order = 1162
lean = ["AlgebraicGeometry.Scheme.Etale.overEquiv", "AlgebraicGeometry.Scheme.IsLocallyConstantSheaf.upperStar", "AlgebraicGeometry.Scheme.isConstant_over_iff_upperStar"]
uses = ["def-constructible-constant", "def-constructible-locally-constant", "lemma-constructible-pullback-constant"]
+++
Let $g\colon Y\to X$ be a morphism and let $\mathcal F\in\shv{\et X}$ be
locally constant. Then $g^*\mathcal F$ is locally constant.

## Proof

Let $(U_i\to X)_i$ be a trivialising datum for $\mathcal F$. The base
change $(U_i\times_XY\to Y)_i$ is an étale cover of $Y$, since étale
morphisms and jointly surjective families are stable under base change.
The restriction of $g^*\mathcal F$ to $\et{U_i\times_XY}$ is the pullback,
along the projection $g_i\colon U_i\times_XY\to U_i$, of the restriction
of $\mathcal F$ to $\et{U_i}$: pullback along $g$ followed by restriction to
the localised site equals restriction followed by pullback along $g_i$,
because both are the sheaf pullback along the composite of the base change
functors, which agree. The restriction of $\mathcal F$ to $\et{U_i}$ is
constant, and pullbacks of constant sheaves are constant by
[lemma-constructible-pullback-constant]. Hence
$(U_i\times_XY\to Y)_i$ is a trivialising datum for $g^*\mathcal F$.
