+++
id = "lem-a1-finite-boundary-weights"
kind = "lemma"
title = "Weights of the cohomology of a finite boundary"
order = 2793
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-punctual-weights", "lem-a1-finite-boundary-cohomology", "lem-a1-punctual-bound-module-mixed", "p-linear-filtration"]
+++
Let $Z_0$ be finite over $k_0$ and let $\mathcal G$ be a
constructible Weil sheaf whose stalks have weights at most $w$. Then
$H_c^0(Z,\mathcal G)$ has weights at most $w$.

## Proof

Evaluation at geometric points gives, as in the proof of
[lem-a1-finite-boundary-cohomology],

$$
H_c^0(Z,\mathcal G)=\bigoplus_{x\in|Z_0|}\mathcal G_{\bar x}^{
\operatorname{Gal}(\overline{\kappa(x)}/\kappa(x))},
$$

and each summand is an
$F_x$-stable submodule of the stalk $\mathcal G_{\bar x}$, whose
eigenvalues are among the eigenvalues of $F_x$ ([p-linear-filtration]): all of them have
weight at most $w$ by hypothesis, so the submodule is mixed of
weights at most $w$ by [lem-a1-punctual-bound-module-mixed].
