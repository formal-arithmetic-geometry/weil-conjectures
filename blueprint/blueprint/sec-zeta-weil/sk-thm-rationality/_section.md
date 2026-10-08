+++
id = "sk-thm-rationality"
kind = "section"
title = "Rationality of the zeta series"
order = 2890
lean = ["AlgebraicGeometry.Scheme.zetaSeries_rational"]
uses = ["sk-def-roots", "sk-def-zeta", "sk-prop-criterion", "sk-prop-euler", "sk-thm-tracetodeterminant"]
+++
*Theorem (sketch).*

Let $X_0/\Fq$ be smooth, proper and geometrically connected of pure dimension
$d$. Then

$$
Z(X_0,T)\in\Q(T)\cap(1+T\Z[[T]]).
$$

## Proof

[sk-thm-tracetodeterminant] factors $Z$ as a finite product of the rational
functions $P_{i,\ell}^{\pm1}$ over $\Ql$, so $Z\in\Ql(T)$; write
$Z=A_\ell/B_\ell$ with $A_\ell,B_\ell\in\Ql[T]$, $B_\ell(0)=1$. By
[sk-prop-criterion] (applied over $\Ql$) the Hankel matrix $\mathcal H(Z)$
has finite rank $r<\infty$. Now all $z_n$ lie in $\Z$ by [sk-prop-euler],
so every $r'\times r'$ minor of $\mathcal H(Z)$ with $r'>r$ is an integer
matrix whose $\Ql$-rank is $<r'$, hence whose determinant is $0$ in $\Z$; rank
is unchanged by field extension, so $\rank_{\Q}\mathcal H(Z)\le r$ as well.
Applying [sk-prop-criterion] over the prime field $\Q$ gives
$Z\in\Q(T)$. Integrality of the coefficients is [sk-prop-euler].

Uses: [sk-def-roots], [sk-def-zeta], [sk-prop-criterion], [sk-prop-euler], [sk-thm-tracetodeterminant]
