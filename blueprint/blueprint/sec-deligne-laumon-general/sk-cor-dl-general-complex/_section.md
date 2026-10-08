+++
id = "sk-cor-dl-general-complex"
kind = "section"
title = "The derived direct-image bound"
order = 2850
lean = ["AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerShriek"]
uses = ["sk-d-dl-general-weights", "sk-thm-dl-general-sheaf"]
+++
*Corollary (sketch).*

If $K_0$ is a bounded constructible Weil complex of weights at most
$w$, then $Rf_{0!}K_0$ has weights at most $w$.

## Proof

In the finite hypercohomology spectral sequence

$$
R^af_{0!}\mathcal H^b(K_0)
\ \Longrightarrow\ \mathcal H^{a+b}(Rf_{0!}K_0),
$$

the term on the left has weights at most $w+b+a$.
Subquotients and extensions give the bound $w+n$ in total degree $n$,
which is precisely the derived convention.

Uses: [sk-d-dl-general-weights], [sk-thm-dl-general-sheaf]
