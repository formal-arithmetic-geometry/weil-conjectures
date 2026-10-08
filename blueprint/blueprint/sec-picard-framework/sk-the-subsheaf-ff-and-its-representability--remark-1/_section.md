+++
id = "sk-the-subsheaf-ff-and-its-representability--remark-1"
kind = "section"
title = "$F$ is a subfunctor of the Hilbert functor"
order = 832
lean = ["AlgebraicGeometry.exists_injective_natTrans_hilbertPresheaf"]
+++
*Remark (sketch).*

The dictionary of [sk-lem-picard-zero-dictionary] ($\cL\mapsto D=Z(s)$)
defines an injective natural transformation
$F\hookrightarrow\Hilb^g_{X/k}$ through which the open subscheme
$W\subseteq\underline{\Hilb}^g_{X/k}$ represents $F$; the inverse is
$D\mapsto\cO(D)\otimes\operatorname{pr}_T^*\sigma_T^*\cO(D)^{-1}$
(the $\sigma$-normalization of $\cO(D)$ on $X_T$, as for $\cL_H$ in
the proof of [sk-thm-picard-f-representable]). This is the precise
sense in which ``$F$ is a subsheaf of the Hilbert functor''.
