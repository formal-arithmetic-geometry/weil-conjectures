+++
id = "sk-thm-weil2"
kind = "section"
title = "Weil conjectures II: integral Frobenius factors"
order = 2929
lean = ["AlgebraicGeometry.Scheme.weil_conjectures", "AlgebraicGeometry.IsWeilFactorization"]
uses = ["sk-def-zeta", "sk-thm-intfactors"]
+++
*Theorem (sketch).*

There are unique $P_i\in\Z[T]$ with $P_i(0)=1$ and
$P_i^{(\ell)}=\det(1-TF_{i,\ell}\mid H^{i}(X,\Ql))$ for every $\ell\ne p$, and
$Z(X_0,T)=\prod_{i=0}^{2d}P_i(T)^{(-1)^{i+1}}$, independently of $\ell$.

## Proof

This is [sk-thm-intfactors], restated as a Weil conjecture.

Uses: [sk-def-zeta], [sk-thm-intfactors]
