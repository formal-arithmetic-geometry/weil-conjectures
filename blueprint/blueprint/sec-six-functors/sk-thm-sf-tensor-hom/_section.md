+++
id = "sk-thm-sf-tensor-hom"
kind = "section"
title = "Tensor–Hom form of the exchange"
order = 2166
uses = ["sk-def-sf-exchanges", "sk-def-sf-operations", "sk-lem-sf-mate", "sk-prop-sf-comparison", "sk-prop-sf-existence", "sk-rem-sf-pf-done", "sk-thm-sf-pf-adic", "sk-thm-sf-pf-field", "sk-thm-sf-pf-finite", "sk-thm-sf-pf-proetale"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_derivedHom_rightDerivedLowerShriek"]
+++
*Theorem (sketch).*

Let $f:X\to Y$ be a separated finite-type morphism of finite-type
$k$-schemes, with $f^!=Rf^!$ the constructible exceptional adjoint of
[sk-def-sf-operations] (vi) (no admissibility datum is assumed), and let
$M\in\Dctf(X,\Lambda)$ and $N\in\Dctf(Y,\Lambda)$. Then there is a canonical isomorphism
$$
Rf_*\RHom_X(M,f^!N)\xrightarrow{\ \sim\ }\RHom_Y(Rf_!M,N),
$$

in the ambient category $D^+(Y,\Lambda)$, natural in $M$ and $N$ and
compatible with finite reduction, scalar extension and shifts.

## Proof

For every $L$ the adjunctions and the tensor–internal-Hom adjunction give a
chain

$$
\begin{aligned}
\operatorname{Hom}_Y\bigl(L,\RHom_Y(Rf_!M,N)\bigr)
&\cong\operatorname{Hom}_Y(Rf_!M\otimes^LL,N)\\
&\cong\operatorname{Hom}_Y\bigl(Rf_!(M\otimes^LLf^*L),N\bigr)\\
&\cong\operatorname{Hom}_X\bigl(M\otimes^LLf^*L,f^!N\bigr)\\
&\cong\operatorname{Hom}_X\bigl(Lf^*L,\RHom_X(M,f^!N)\bigr)\\
&\cong\operatorname{Hom}_Y\bigl(L,Rf_*\RHom_X(M,f^!N)\bigr),
\end{aligned}
$$

in which the second isomorphism is the *inverse* of the projection
formula at the coefficient stage of $\Lambda$ — [sk-thm-sf-pf-finite] at
$\Lambda=A_{E,n}$, and [sk-thm-sf-pf-adic], [sk-thm-sf-pf-field],
[sk-thm-sf-pf-proetale] at the remaining stages, all stated in the ambient
$D^+$ and collected in [sk-rem-sf-pf-done] — and the third is the adjunction
$Rf_!\dashv Rf^!$ of [sk-prop-sf-existence](c), valid because
$M\otimes^LLf^*L$ is bounded below of étale origin when $L$ is. The chain
is natural in $L$ ranging over the bounded-below complexes of étale origin,
a full subcategory containing both sides (each is the comparison image of the
corresponding complex on the étale site, [sk-prop-sf-comparison]), so
the two objects represent the same functor there and Yoneda gives the
isomorphism.

Uses: `\Cref{sk-def-sf-exchanges}`, `\Cref{sk-def-sf-operations}`, `\Cref{lem-sf-mate}`, `\Cref{sk-thm-sf-pf-finite}`, `\Cref{sk-thm-sf-pf-adic}`, `\Cref{sk-thm-sf-pf-field}`, `\Cref{sk-thm-sf-pf-proetale}`, `\Cref{sk-rem-sf-pf-done}`, `def-weil-derived-pullback-tensor-hom`
