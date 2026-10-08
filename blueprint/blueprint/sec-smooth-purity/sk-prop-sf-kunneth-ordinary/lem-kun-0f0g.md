+++
id = "lem-kun-0f0g"
kind = "lemma"
title = "Projection formula for proper morphisms"
order = 1736
uses = ["def-kun-cd", "def-kun-projection-formula-map", "def-kun-truncations", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "def-weil-pbc-scheme-conventions", "lem-kun-0f10", "lem-kun-0f11", "lem-kun-bounded-flat-replacement", "lem-kun-complex-colimit-hocolim", "lem-kun-derived-tensor-direct-sums", "lem-kun-derived-tensor-triangulated", "lem-kun-hocolim-truncations"]
+++
Let $f:X\to Y$ be a
proper morphism and
$\Lambda$ a torsion ring. For $E\in D(X_{\Et},\Lambda)$ and
$K\in D(Y_{\Et},\Lambda)$, the canonical projection-formula morphism

$$
\mathrm{PF}_f(E,K):\quad
Rf_*E\kunotimes{\Lambda}K\longrightarrow
Rf_*(E\kunotimes{\Lambda}f^{-1}K)
$$

of [def-kun-projection-formula-map] is an isomorphism.

## Proof

Write $\Lambda=\kunZn$. Both sides of
[def-kun-projection-formula-map] are triangulated functors of
$K\in D(Y_{\Et},\Lambda)$
([lem-kun-derived-tensor-triangulated]). For $K=\Lambda$ in degree zero the map
is the identity constraint, hence an isomorphism, and the same holds
for every bounded complex of free $\Lambda$-module sheaves, both
sides being compatible with finite direct sums and shifts. A
bounded-above $K$ may be replaced by a bounded-above complex of flat
sheaves ([lem-kun-bounded-flat-replacement]) and written as the
filtered colimit of its stupid truncations
([def-kun-truncations]), which is a homotopy colimit
([lem-kun-complex-colimit-hocolim]); the left hand side commutes
with homotopy colimits
([lem-kun-derived-tensor-direct-sums]), and the right hand side
does too, because $f$ proper of finite type over a field has
$\kuncd(f)<\infty$ by [lem-kun-0f10](1) and therefore $Rf_*$
preserves direct sums by [lem-kun-0f11] ([def-kun-cd] for
the dimension predicate). An arbitrary $K$ is the homotopy colimit
of its truncations $\tau_{[-N,N]}K$
([lem-kun-hocolim-truncations]), which are bounded, and the same
two commutation statements reduce to the bounded-above case. Hence
$\mathrm{PF}_f(E,K)$ is an isomorphism in general; the identifications
used are those of [def-weil-pbc-direct-image] and
[def-weil-pbc-inverse-image].
