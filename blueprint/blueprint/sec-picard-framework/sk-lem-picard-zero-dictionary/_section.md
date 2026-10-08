+++
id = "sk-lem-picard-zero-dictionary"
kind = "section"
title = "The zero-scheme dictionary"
order = 825
uses = ["sk-cor-picard-degree-g", "sk-def-av-jacobian", "sk-def-av-pic"]
lean = ["AlgebraicGeometry.exists_isEffectiveCartierCenter_hilbertPresheaf"]
+++
*Lemma (sketch).*

Let $\cL\in F(T)$, $\cN$ invertible with
$Rf_{T,*}\cL\cong\cN[0]$, and let $s\in H^0(X_T,\cL\otimes f_T^*\cN^{-1})$ be the adjoint section. Then
$D:=Z(s)\subseteq X_T$ is a relative effective Cartier divisor on
$X_T/T$, finite locally free of *degree $g$* over $T$.

## Proof

*(This is the seam $S_2$.)* On a fibre $X_t$ the data
$Rf_{t,*}\cL_t\cong\cN_t[0]$ give $h^0(X_t,\cL_t)=1$ and
$h^q=0$ for $q>0$, so by [sk-cor-picard-degree-g]:

$$
\deg(\cL_t)=\chi(\cL_t)-\chi(\cO_{X_t})=1-(1-g)=g .
$$

*(Two instances of [sk-thm-picard-rr] (G) and the DVR argument.)*
$s_t\neq0$ (it is the identity of $\cN_t$), and over the integral
$X_t$ its zero set is a finite effective Cartier divisor of degree
$\deg\cL_t=g$ (the local rings at its points are DVRs); the Cartier
criterion promotes this to the relative statement and gives that
$D\to T$ is finite locally free of degree $g$.
