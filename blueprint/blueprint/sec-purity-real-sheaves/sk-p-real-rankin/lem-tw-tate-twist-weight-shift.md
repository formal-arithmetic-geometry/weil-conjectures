+++
id = "lem-tw-tate-twist-weight-shift"
kind = "lemma"
title = "Weight shift under a Tate twist"
order = 2658
uses = ["def-coefficient-twists-detailed", "def-weil-finite-field-fiber", "def-weil-frobenius-coefficient-twists", "def-weil-frobenius-module-weights", "def-weil-punctual-weights", "def-weil-weil-sheaf-complex", "lem-tw-multiplicativity"]
+++
Fix the finite-field datum
$(p,a,q,k_0,k)$ and an isomorphism
$\iota:\Qlb\xrightarrow{\sim}\mathbf C$ as in
[def-weil-punctual-weights]. If a lisse
Weil sheaf $\mathcal F$ is
punctually $\iota$-pure of weight $w$, then its
Tate twist $\mathcal F(n)$ is
punctually $\iota$-pure of weight $w-2n$, for every
$n\in\mathbf Z$. The same shift holds for upper weight bounds: if
$\mathcal F$ is $\iota$-mixed of weights at most $w$, then
$\mathcal F(n)$ is $\iota$-mixed of weights at most $w-2n$.

## Proof

At a closed point $y$ of degree $m$, the local Frobenius operator
$F_y$ of [def-weil-punctual-weights] acts on the twist
stalk $\mathcal F(n)_{\bar y}$ as $q^{-mn}$ times the operator on
$\mathcal F_{\bar y}$, by the Frobenius-on-twists normalization of
[def-weil-frobenius-coefficient-twists] (the local operator is the
$m$-fold iterate of the global geometric Frobenius). Hence the
eigenvalues of $\mathcal F(n)_{\bar y}$ are the
$q^{-mn}\alpha$, $\alpha$ running over the eigenvalues of
$F_y$ on $\mathcal F_{\bar y}$, and by
[lem-tw-multiplicativity] and $q_y=q^m$,

$$
|\iota(q^{-mn}\alpha)|=q^{-mn}q^{mw/2}=q_y^{(w-2n)/2},
$$

which is the punctual purity of weight $w-2n$ of
[def-weil-punctual-weights]. For the mixed statement, apply the
pure statement to the graded pieces of a weight filtration of
$\mathcal F$ (the twist is exact and preserves the filtration by
[def-weil-frobenius-module-weights] at the level of stalk modules)
and use the same shift on each piece.
