+++
id = "sk-thm-sf-pf-adic"
kind = "section"
title = "Projection formula: the derived-complete stage"
order = 2095
uses = ["sk-def-sf-operations", "sk-prop-sf-pf-reduction"]
lean = ["AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral"]
+++
*Theorem (sketch).*

Let $K,L$ be derived-complete $\Dctf$-objects over $\mathcal O_E$ of finite Tor
amplitude, with finite reductions $K_n,L_n$. Then the maps
$\operatorname{PF}_{f,K_n,L_n}$ form a morphism of normalized systems and
realize a canonical isomorphism $\operatorname{PF}_{f,K,L}$ over
$\mathcal O_E$, compatible with all finite reductions.

## Proof

Each finite-level map is an isomorphism by [sk-thm-sf-pf-finite], and the
maps are compatible under reduction by [sk-prop-sf-pf-reduction], with
uniform bounds inherited from $K$ and $L$ (finite Tor amplitude of a
derived-complete object is uniform in $n$). Derived completeness and this
compatibility are exactly the hypothesis of the uniform-tower reconstruction
lem:weil-pbc-reconstruction-uniform-tower, which realizes the system as a
morphism of derived-complete complexes with the given reductions; it is an
isomorphism because its reductions are and reduction is conservative on
derived-complete complexes of finite Tor amplitude.

Uses: `\Cref{prop-sf-pf-reduction}`, `def-weil-derived-complete-integral-detailed`, `lem-weil-pbc-reconstruction-uniform-tower`
