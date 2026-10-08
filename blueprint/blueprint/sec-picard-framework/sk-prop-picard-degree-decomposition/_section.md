+++
id = "sk-prop-picard-degree-decomposition"
kind = "section"
title = "Degree decomposition of the Picard scheme"
order = 840
uses = ["sk-def-av-jacobian", "sk-def-av-pic", "sk-prop-picard-pic-split", "sk-thm-picard-main", "sk-thm-picard-rr", "sk-thm-picard-semicon"]
lean = ["AlgebraicGeometry.picardFunctorDegree", "AlgebraicGeometry.exists_decomposition_picardFunctor"]
+++
*Proposition (sketch).*

The function $t\mapsto\deg\cL_t$ is locally constant on
$\underline{\Pic}_{C/k}$. Hence

$$
\underline{\Pic}_{C/k}=\coprod_{d\in\Z}\underline{\Pic}^d_{C/k},
\qquad
\underline{\Pic}^d_{C/k}:=\{t:\deg\cL_t=d\},
$$

each $\underline{\Pic}^d_{C/k}$ is open and closed and represents the
subfunctor of classes of fibrewise degree $d$, $\underline{\Pic}^0_{C/k}$
is an open and closed subgroup scheme, and tensoring with
$\cO_C(dP)$ is an isomorphism of schemes
$\underline{\Pic}^0_{C/k}\xrightarrow{\sim}\underline{\Pic}^d_{C/k}$.

## Proof

The projection $C\times_k\underline{\Pic}_{C/k}\to\underline{\Pic}_{C/k}$
is proper and flat and $\cL_{\mathrm{univ}}$ is invertible, hence flat
over the base. As in the proof of [sk-thm-picard-semicon], locally on
the base $R\mathrm{pr}_*\cL_{\mathrm{univ}}$ is represented by a bounded
complex of finite free modules whose formation commutes with base change
to the fibres; so $\chi(\cL_t)$ is the alternating sum of the ranks of
that complex and is locally constant in $t$. By
[sk-thm-picard-rr] (RR), $\chi(\cO_{C_{\kappa(t)}})=1-g$ does not depend
on $t$, so $\deg\cL_t=\chi(\cL_t)-(1-g)$ is locally constant, which
gives the decomposition into open and closed pieces. A $T$-point
factors through $\underline{\Pic}^d_{C/k}$ exactly when all its fibres
have degree $d$, so $\underline{\Pic}^d_{C/k}$ represents that subfunctor.
The degree is additive under $\otimes$ and $\deg\cO_C=0$, so
$\underline{\Pic}^0_{C/k}$ contains the unit and is stable under the
multiplication and the inverse; it is a subgroup scheme. Finally,
$\cO_C(dP)$ is a $k$-point of $\underline{\Pic}^d_{C/k}$, translation by
a $k$-point is an automorphism of the group scheme
$\underline{\Pic}_{C/k}$ with inverse the translation by
$\cO_C(-dP)$, and it adds $d$ to the degree.

Uses: [sk-prop-picard-pic-split], [sk-thm-picard-main], [sk-thm-picard-rr], [sk-thm-picard-semicon]
