+++
id = "lem-wf-constant-twist-cohomology"
kind = "lemma"
title = "Projection formula for a constant twist"
order = 2772
uses = ["def-weil-pbc-scheme-conventions", "def-wf-constant-weil-twist", "fix-prop-projection-formula"]
+++
In the setting of [def-wf-constant-weil-twist], let
$h:X_0\to Y_0$ be a
separated finite-type
morphism of separated finite-type $k_0$-schemes, let
$\mathcal K$ be a constructible $\Qlb$-Weil complex on $X_0$, and
let $\mathcal B_b$ be the
constant Weil twist on $Y_0$.
There is a Frobenius-compatible isomorphism

$$
Rh_!\bigl(\mathcal K\otimes h^*\mathcal B_b\bigr)
\;\cong\;Rh_!\mathcal K\otimes\mathcal B_b.
$$

## Proof

This is the projection formula for the compact-support direct image,
[fix-prop-projection-formula] of the framework chapter, applied to the
constant rank-one twist $\mathcal B_b$ of
[def-wf-constant-weil-twist]; the projection formula is compatible
with the Frobenius descent data, so the identification is
Frobenius-compatible.
