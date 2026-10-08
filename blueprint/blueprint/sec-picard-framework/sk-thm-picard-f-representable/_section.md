+++
id = "sk-thm-picard-f-representable"
kind = "section"
title = "$F$ is representable"
order = 828
uses = ["sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage"]
+++
*Theorem (sketch).*

$F$ is representable by an open subscheme of
$\underline{\Hilb}^g_{X/k}$.

## Proof

Let $H:=\underline{\Hilb}^g_{X/k}$ and
$\cL_H:=\cO(D_{\mathrm{univ}})\otimes \operatorname{pr}_H^*\sigma_H^*\cO(D_{\mathrm{univ}})^{\otimes-1}$
(the normalized universal module, an element of $G(H)$ by Yoneda).
Being open ([sk-lem-picard-f-open]), $F$ determines a maximal open
$W\subseteq H$ with $\cL_H|_W\in F(W)$, and the induced natural
transformation $h_W\to F$ is an isomorphism: the inverse is
$\cL\mapsto m$ where $m:T\to H$ classifies $D=Z(s)$ of
[sk-lem-picard-zero-dictionary], and
$(m\times\mathrm{id})^*\cL_H\cong\cL$ by the computation of the
adjoint section and the $\sigma$-normalization.
