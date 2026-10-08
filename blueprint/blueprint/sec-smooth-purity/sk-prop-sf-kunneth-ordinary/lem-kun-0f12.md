+++
id = "lem-kun-0f12"
kind = "lemma"
title = "Tensor product with a constant complex"
order = 1733
uses = ["def-kun-cd", "def-kun-derived-tensor", "def-kun-truncations", "def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions", "lem-kun-0f11", "lem-kun-bounded-flat-replacement", "lem-kun-complex-colimit-hocolim", "lem-kun-derived-tensor-direct-sums", "lem-kun-derived-tensor-triangulated", "lem-kun-hocolim-truncations"]
+++
Let $X$ be a
quasi-compact and
quasi-separated scheme with $\kuncd(X)<\infty$ and let $\Lambda$ be
a torsion ring. For $E\in D(X_{\Et},\Lambda)$ and
$K\in D(\Lambda)$, the canonical map

$$
\RGamma(X_{\Et},E)\kunotimes{\Lambda}K\longrightarrow
\RGamma\bigl(X_{\Et},E\kunotimes{\Lambda}\underline{K}\bigr)
$$

is an isomorphism.

## Proof

Both sides are triangulated functors in $K\in D(\Lambda)$
([lem-kun-derived-tensor-triangulated],
[def-kun-derived-tensor], [def-weil-pbc-etale-cohomology]),
and they agree for $K=\Lambda$ in degree zero. If $K$ is a bounded
complex of free $\Lambda$-modules, both sides commute with finite
direct sums and shifts, so the map is an isomorphism by the
degreewise comparison of the (finite, in each degree) direct sums.
For $K$ bounded above we may replace it by a bounded-above complex of
free $\Lambda$-modules ([lem-kun-bounded-flat-replacement]) and
write it as the filtered colimit of its stupid truncations
([def-kun-truncations]); the filtered colimit of complexes is a
homotopy colimit ([lem-kun-complex-colimit-hocolim]), the left
hand side commutes with homotopy colimits because the derived tensor
product preserves direct sums
([lem-kun-derived-tensor-direct-sums]), and the right hand side
does because $\kuncd(X)<\infty$ forces $\RGamma(X_{\Et},-)$ to
preserve direct sums, hence homotopy colimits, by
[lem-kun-0f11] ([def-kun-cd] for the dimension predicate).
For arbitrary $K$ write $K=\operatorname{hocolim}_N\tau_{\le N}K$
([lem-kun-hocolim-truncations]) and apply the same two commutation
statements; this reduces to the bounded-above case just proved. Hence
the canonical map is an isomorphism in general.
