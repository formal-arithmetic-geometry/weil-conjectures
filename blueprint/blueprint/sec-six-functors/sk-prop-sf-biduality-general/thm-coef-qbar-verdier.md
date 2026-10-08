+++
id = "thm-coef-qbar-verdier"
kind = "theorem"
title = "Verdier biduality at algebraically closed coefficients"
order = 2154
uses = ["def-weil-algebraically-closed-coefficients", "lem-coef-rational-operations", "lem-coef-rational-retract-evaluation", "prop-weil-pbc-common-stage-calculus", "prop-weil-pbc-descent-functors", "thm-coef-rational-verdier"]
+++
The finite-field dualities and their scalar-extension comparisons
induce an exact $\Qlb$-linear anti-equivalence

$$
D_{X,\Qlb}:D^b_c(X,\Qlb)^{\mathrm{op}}
\xrightarrow{\sim}D^b_c(X,\Qlb),
\qquad (E,K)\longmapsto(E,D_{X,E}K).
$$

It is the internal Hom into $\omega_{X,\Qlb}=Ra_X^!\Qlb$
in the common-stage category. Evaluation and biduality descend,
giving a natural isomorphism
$K\xrightarrow{\sim}D_{X,\Qlb}D_{X,\Qlb}K$.
For a separated finite-type $f:X\to Y$, the same passage
gives the constructible adjunction $Rf_!\dashv Rf^!$ and
$Rf^!=D_Xf^*D_Y$. All of these maps are compatible with
finite scalar extension and with retracts.

## Proof

Apply [prop-weil-pbc-descent-functors] to the opposite
categories and the comparisons of [thm-coef-rational-verdier].
For clarity, a morphism from $(E,K)$ to $(F,L)$ represented
at a common finite field $M$ by
$u:T_{M/E}K\to T_{M/F}L$ is sent to

$$
T_{M/F}D_FL\xrightarrow{\beta_{M/F}}
D_MT_{M/F}L\xrightarrow{D_Mu}
D_MT_{M/E}K\xrightarrow{\beta_{M/E}^{-1}}T_{M/E}D_EK.
$$

The unit and associator equations for $\beta$ show that this
is independent of the common field and of the representative;
these are exactly the equivalences on morphisms in
[def-weil-algebraically-closed-coefficients]. Exactness
and linearity follow at a common finite stage.

The scalar-compatible evaluations and $\delta$'s descend by
the same construction. The inverse of each $\delta$ is
already present at its finite stage, so the descended map is an
isomorphism, proving the anti-equivalence. The tensor–Hom and
exceptional adjunctions of [lem-coef-rational-operations]
also descend: represent their finitely many objects and maps at
one common stage as in [prop-weil-pbc-common-stage-calculus],
apply the finite-stage adjunction, and use its coefficient
compatibility to pass to the filtered colimit of Hom groups.
For the exceptional functor this compatibility also follows
directly from $Rf^!=D_Xf^*D_Y$, since pullback is compatible
with scalar extension. This proves the asserted identification
of $\omega$, internal Hom, and $Rf^!$, including their
units and counits. Restriction to retracts is
[lem-coef-rational-retract-evaluation], performed at a
finite common stage. No tensor product with an infinite
topological coefficient extension is required by this proof.
