+++
id = "lem-pd-descent-cocycle"
kind = "lemma"
title = "The cocycle condition is automatic"
order = 861
uses = ["cor-pd-pic0-base-change", "def-pc-base-change", "def-pd-descent-datum", "lem-pd-canonical-descent-datum", "lem-sc-jacobian-unique"]
+++
In the situation of [lem-pd-canonical-descent-datum], the isomorphism
$\varphi$ satisfies the cocycle condition of [def-pd-descent-datum].

## Proof

Write $X_3=X\times_YX\times_YX=\Spec(k_s\otimes_kk_s\otimes_kk_s)$ for the
triple fibre product of [def-pc-base-change] and let
$\mathrm{pr}_{01},\mathrm{pr}_{02},\mathrm{pr}_{12}:X_3\to X_2$ be the
projections, so that $\varphi$ is the isomorphism of
[lem-pd-canonical-descent-datum]. By
[cor-pd-pic0-base-change] all six pullbacks of $J_s$ to
$X_3$ represent one and the same functor, namely the restriction of
$\operatorname{Pic}^0_{C/k}$ to the slice over $X_3$. Both composites
$\mathrm{pr}_{02}^*\varphi$ and
$\mathrm{pr}_{12}^*\varphi\circ\mathrm{pr}_{01}^*\varphi$ are isomorphisms
between two representing objects of that functor which respect the
representing identifications, so they agree by the uniqueness statement of
[lem-sc-jacobian-unique] (applied over $X_3$). This is the cocycle
condition of [def-pd-descent-datum].
