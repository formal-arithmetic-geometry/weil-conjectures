+++
id = "sk-thm-rh"
kind = "section"
title = "Riemann hypothesis for smooth proper schemes"
order = 2911
lean = ["AlgebraicGeometry.Scheme.weil_conjectures", "Polynomial.IsUniversallyPureOfWeight"]
uses = ["sk-def-roots", "sk-def-zeta", "sk-prop-rootpurity", "sk-thm-intfactors"]
+++
*Theorem (sketch).*

Let $X_0/\Fq$ be smooth, proper and geometrically connected of pure dimension
$d$, and let $P_i\in\Z[T]$ be the integral Frobenius factors of
[sk-thm-intfactors]. Then every reciprocal root $\alpha$ of $P_i$ is an
algebraic integer and a $q$-Weil number of weight $i$:

$$
|\tau(\alpha)|=q^{i/2}
\qquad\text{for every embedding }\tau:\Q(\alpha)\hookrightarrow\C .
$$

Equivalently, $|\tau(\beta)|=q^{-i/2}$ for every ordinary root $\beta$.

## Proof

By [sk-thm-intfactors], $P_i\in\Z[T]$ with $P_i(0)=1$, so the reversed
polynomial $P_i^{\#}$ is monic with integer coefficients and its roots — the
reciprocal roots — are algebraic integers. Fix a reciprocal root $\alpha$
of $P_i$. Every embedding $\tau:\Q(\alpha)\hookrightarrow\C$ extends to an
isomorphism $\Qlb\cong\C$, and [sk-prop-rootpurity], applied through that
isomorphism, gives $|\tau(\alpha)|=q^{i/2}$. This is exactly the $q$-Weil
condition of [sk-def-roots]; inverting gives the ordinary-root form.

Uses: [sk-def-roots], [sk-def-zeta], [sk-prop-rootpurity], [sk-thm-intfactors]
