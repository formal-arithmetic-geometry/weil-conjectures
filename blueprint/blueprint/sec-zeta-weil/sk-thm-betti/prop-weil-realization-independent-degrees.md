+++
id = "prop-weil-realization-independent-degrees"
kind = "theorem"
title = "Realization-independent degrees of the integral factors"
order = 2925
tags = ["latex:proposition"]
uses = ["def-weil-ordinary-compact-cohomology", "def-weil-smooth-proper-cohomological-family", "prop-arithmetic-roots", "prop-integral-recovery"]
+++
In the situation of [prop-arithmetic-roots], for every prime
$\ell\neq p$,

$$
r_i=\dim_{\Ql}H^i(X,\Ql),
$$

where $H^i(X,\Ql)$ is the
ordinary cohomology group
and $r_i=\deg P_i$; the integral Frobenius factor $P_i$ and its degree
$r_i$ are therefore independent of the chosen ell-adic realization.

## Proof

The degree equality is the degree assertion in
[def-weil-smooth-proper-cohomological-family], namely
$\deg P_{i,\ell}=\dim_{\Ql}H^i(X,\Ql)$ for the ordinary cohomology groups
of [def-weil-ordinary-compact-cohomology], together with the
scalar-extension identity $P_i^{(\ell)}=P_{i,\ell}$ and the uniqueness of
$P_i$ in [prop-integral-recovery]; scalar extension preserves
degree, so $r_i=\deg P_i=\dim_{\Ql}H^i(X,\Ql)$, and the factor $P_i$ as
well as its degree $r_i$ are independent of the chosen ell-adic
realization.
