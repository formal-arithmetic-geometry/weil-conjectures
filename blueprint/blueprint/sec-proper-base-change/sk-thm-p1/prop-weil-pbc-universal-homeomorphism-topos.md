+++
id = "prop-weil-pbc-universal-homeomorphism-topos"
kind = "theorem"
title = "Topological invariance of the small etale topos"
order = 1167
lean = ["AlgebraicGeometry.Etale.cohomologyEquiv", "AlgebraicGeometry.Etale.cohomologyMap_bijective", "AlgebraicGeometry.Etale.isEquivalence_upperStar", "AlgebraicGeometry.Etale.sheafEquivalence"]
tags = ["latex:proposition"]
uses = ["def-pc-ext", "lemma-constructible-pullback-constant", "lemma-weil-pbc-universal-homeomorphism-coverings", "lemma-weil-pbc-universal-homeomorphism-site-equivalence"]
+++
Let $u:X_0\to X$ be a universal homeomorphism. Pullback along $u$ is an
equivalence between the small etale topos of $X$ and that of $X_0$, and for
every abelian sheaf $F$ on $X_{\mathrm{et}}$ and every $n$ it induces an
isomorphism

$$
H^n(X_{\mathrm{et}},F)\xrightarrow{\sim}H^n(X_{0,\mathrm{et}},u^{-1}F).
$$

This is Tag `03SI`.

## Proof

Base change is an equivalence of the underlying categories and matches the
covering families, hence is an equivalence of sites; so restriction along it
is an equivalence of the categories of sheaves, and pullback, being its left
adjoint, is a quasi-inverse. Cohomology is the $\operatorname{Ext}$-groups
out of the constant sheaf $\mathbf Z$, and an exact equivalence carrying the
constant sheaf to the constant sheaf induces an isomorphism on those groups.
