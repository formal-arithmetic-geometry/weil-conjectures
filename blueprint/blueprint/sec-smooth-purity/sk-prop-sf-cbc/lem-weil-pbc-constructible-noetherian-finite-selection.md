+++
id = "lem-weil-pbc-constructible-noetherian-finite-selection"
kind = "lemma"
title = "Noetherian finite selection of stalk tests"
order = 1604
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "lem-weil-pbc-irreducible-lisse-strata", "lem-weil-pbc-lisse-generic-kernel", "lemma-weil-pbc-geometric-stalk-conservative", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $X$ be Noetherian, let $F$ be a constructible abelian etale sheaf, and let
$(\phi_\lambda:F\to G_\lambda)_{\lambda\in L}$ be a family of maps to
arbitrary abelian etale sheaves. Assume that for every geometric point $\bar
x$ and every $0\neq v\in F_{\bar x}$, some $\lambda$ satisfies
$(\phi_\lambda)_{\bar x}(v)\neq0$. Then a finite subset $L_0\subset L$ makes

$$
 (\phi_\lambda)_{\lambda\in L_0}:
 F\longrightarrow\bigoplus_{\lambda\in L_0}G_\lambda
$$

a monomorphism. In particular, the conclusion holds if at each geometric point
some single $\phi_\lambda$ is injective.

## Proof

Choose the finite partition of [lem-weil-pbc-irreducible-lisse-strata], and a
geometric generic point $\bar\eta_i$ of each $S_i$. The group
$F_{\bar\eta_i}$ is finite. For each of its nonzero elements choose one
$\phi_\lambda$ detecting it, and let $L_i$ be the resulting finite set of
indices. The map

$$
 F|_{S_i}\longrightarrow
 \bigoplus_{\lambda\in L_i}G_\lambda|_{S_i}
$$

is injective at $\bar\eta_i$, hence is a monomorphism on all of $S_i$ by
[lem-weil-pbc-lisse-generic-kernel]. Take $L_0=\bigcup_iL_i$. At any geometric
point of $X$, projection to the summands indexed by its stratum's $L_i$ shows
that the $L_0$-map is injective. Exactness of the geometric stalk functors
makes every stalk of its kernel zero; conservativity of geometric stalks then
makes the kernel zero. No finiteness or constructibility of the target sheaves
is needed.
