+++
id = "sk-c-dl-a1-hc1"
kind = "section"
title = "The degree-one estimate for an irreducible factor"
order = 2780
uses = ["sk-p-dl-a1-fourier-weight", "sk-p-dl-a1-middle", "sk-p-linear-filtration", "sk-p-real-semi", "sk-prop-stalk"]
lean = ["AlgebraicGeometry.hasWeightsAtMost_compactlySupportedCohomology_one"]
+++
*Corollary (sketch).*

If $M$ is nonexceptional and pure of weight $w$, then
$H_c^1(A,j_*M)$ has weights at most $w+1$. In particular this holds
for every irreducible, non-geometrically-constant $M$ unramified at infinity.

## Proof

Semicontinuity bounds the weights of $j'_*M'$ by $v\le w+1$ even
at singular points. At $0$ the Fourier kernel is trivial, and the
stalk formula, including both shifts, gives

$$
\bigl(\DLAFT_\psi(j_*M[1])\bigr)_{\bar0}
\simeq R\Gamma_c(A,j_*M)[2],\qquad
(j'_*M')_{\bar0}\simeq H_c^1(A,j_*M).
$$

This is Frobenius-equivariant. The last assertion follows from the
nonexceptionality test in [sk-p-dl-a1-middle].

Uses: [sk-p-dl-a1-fourier-weight], [sk-p-dl-a1-middle], [sk-p-real-semi], [sk-prop-stalk]
