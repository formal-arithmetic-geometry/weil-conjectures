+++
id = "sk-thm-sf-internal-hom-pullback"
kind = "section"
title = "Internal Hom versus pullback for a site-perfect first variable"
order = 2162
uses = ["sk-def-sf-operations"]
lean = ["AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom"]
+++
*Theorem (sketch).*

Let $\Lambda=A_{E,n}$, let $g:Y'\to X$ be a morphism of finite-type
$k$-schemes, let $M\in D(X,\Lambda)$ be site-perfect — locally on the site,
a bounded complex of finite free $\Lambda$-modules — and let
$N\in\Dctf(X,\Lambda)$. Then the canonical comparison

$$
Lg^*\RHom_\Lambda(M,N)\ \xrightarrow{\ \sim\ }\
\RHom_\Lambda\bigl(Lg^*M,Lg^*N\bigr)
$$

is an isomorphism, natural in both variables and compatible with shifts and
with distinguished triangles in $N$.
Chapter 19, thm:trf-internal-hom-pullback: locally $M$ is a bounded
complex of finite free modules, so the termwise identity
$\operatorname{Hom}(P^i,N^j)=(P^i)^\vee\otimes N^j$ gives
$M^\vee\otimes^L_\Lambda N\cong\RHom_\Lambda(M,N)$ with finitely many summands
in each total degree, and both sides of the displayed map commute with
$Lg^*$.

Uses: `\Cref{sk-def-sf-operations}`, `thm-trf-internal-hom-pullback`
