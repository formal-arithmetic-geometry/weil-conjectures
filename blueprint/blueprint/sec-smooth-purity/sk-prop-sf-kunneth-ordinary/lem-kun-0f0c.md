+++
id = "lem-kun-0f0c"
kind = "lemma"
title = "Proper base change with $\\kunZn$-coefficients"
order = 1739
uses = ["def-kun-cd", "def-kun-truncations", "def-kun-unbounded-exchange", "def-weil-pbc-scheme-conventions", "lem-kun-0f10", "lem-kun-0f11", "lem-kun-hocolim-truncations", "lem-kun-unbounded-exchange-natural", "thm-weil-pbc-bounded-below"]
+++
Let $f:X\to Y$ be a
proper morphism of schemes,
let $g:Y'\to Y$ be any morphism, set $X'=Y'\times_YX$, and write
$f':X'\to Y'$ and $g':X'\to X$ for the projections. For
$K\in D(X_{\Et},\kunZn)$, the exchange morphism of
[def-kun-unbounded-exchange]

$$
\Ex_{\square,K}:g^{-1}Rf_*K\longrightarrow Rf'_*(g')^{-1}K
$$

is an isomorphism.

## Proof

Write $K=\operatorname{hocolim}_N\tau_{[-N,N]}K$
([def-kun-truncations], [lem-kun-hocolim-truncations]). Each
$\tau_{[-N,N]}K$ is bounded, hence bounded below with torsion
cohomology, so the exchange morphism is an isomorphism for it by
[thm-weil-pbc-bounded-below]. The exchange morphism of
[def-kun-unbounded-exchange] is natural in $K$
([lem-kun-unbounded-exchange-natural]), and both sides
commute with homotopy colimits: $g^{-1}$ is exact, and $Rf_*$,
$Rf'_*$ preserve direct sums because $f$ and $f'$ are proper
morphisms of finite type over a field, so that $\kuncd(f),\kuncd(f')< \infty$ by [lem-kun-0f10](1) and [lem-kun-0f11] applies
([def-kun-cd]). Passing to the homotopy colimit therefore gives
the assertion for arbitrary $K$.
