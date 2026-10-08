+++
id = "thm-sf-pf-adic"
kind = "theorem"
title = "Derived-complete reconstruction over $\\mathcal O_E$"
order = 2096
uses = ["def-sf-datum", "def-sf-pf", "def-weil-derived-complete-integral-detailed", "lem-weil-pbc-reconstruction-uniform-tower", "prop-sf-pf-reduction", "thm-sf-pf-finite"]
+++
In the setting of [def-sf-datum], let $K,L$ be derived-complete
$D^b_{ctf}$-objects over $\mathcal O_E$ of finite Tor amplitude with finite
reductions $K_n,L_n$. Then the maps $\operatorname{PF}_{f,K_n,L_n}$ form a
morphism of normalized systems and realize a canonical isomorphism
$\operatorname{PF}_{f,K,L}$ over $\mathcal O_E$, compatible with all finite
reductions.

## Proof

The projection transformation is that of [def-sf-pf] and derived
completeness is that of [def-weil-derived-complete-integral-detailed].
By [thm-sf-pf-finite] each finite-level map is an isomorphism, and by
[prop-sf-pf-reduction] the maps are mutually compatible under
reduction, with uniform bounds and amplitudes inherited from $K$ and $L$
(finite Tor amplitude of a derived-complete object is uniform in $n$).
Derived completeness of the four complexes in the square together with this
compatibility is the hypothesis of the uniform-tower reconstruction of
[lem-weil-pbc-reconstruction-uniform-tower], which realizes the system
as a morphism of derived-complete $\mathcal O_E$-complexes with the given
reductions; it is an isomorphism because its reductions are isomorphisms
and the reduction functors are conservative on derived-complete complexes
of finite Tor amplitude. Finally, the realized map agrees with the
mate-theoretic projection transformation, since both reduce levelwise to
$\operatorname{PF}_{f,K_n,L_n}$ and reductions are conservative.
