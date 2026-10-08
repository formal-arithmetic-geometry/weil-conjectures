+++
id = "lem-weil-pbc-proper-open-comparison-composition"
kind = "lemma"
title = "Composition of proper-open comparison maps"
order = 1483
uses = ["def-weil-pbc-extension-by-zero", "def-weil-pbc-proper-open-comparison", "lem-weil-pbc-derived-open-restriction", "lem-weil-pbc-proper-open-identification", "lem-weil-pbc-proper-open-section"]
+++
Let $u:T_1\to T_2$ and $v:T_2\to T_3$ be proper maps with
open immersions $j_i:X\hookrightarrow T_i$ satisfying
$u j_1=j_2$ and $v j_2=j_3$. For $K\in D^+(X_{\Et},\Lambda)$
with finite $\Lambda$, the maps of
the comparison-map
construction satisfy

$$
\alpha_{vu,K}
= (Rv_*\alpha_{u,K})\circ\alpha_{v,K},
$$

under the canonical identification $R(vu)_*=Rv_*Ru_*$.
For the identity map the comparison is the identity.

## Proof

Both sides have source $j_{3!}K$. By the adjunction in
[def-weil-pbc-extension-by-zero], it suffices to compare their
restrictions to $X$. Apply
[lem-weil-pbc-derived-open-restriction] successively along
$v$ and $u$. In each inverse image of $X$, the distinguished
component $X$ is open and closed by
[lem-weil-pbc-proper-open-section], and all the complexes
$j_{i!}K$ vanish on the complementary components. Restriction of the
two composites to this component is therefore the identity of $K$.
The same is true for $\alpha_{vu,K}$, whose comparison isomorphism is
the one of [lem-weil-pbc-proper-open-identification] for the
composite proper map, by
[def-weil-pbc-proper-open-comparison]. The section identifications
in the open-restriction lemma agree for composite maps, so these are
the same adjoint morphism. This proves the displayed identity.
For $u=\operatorname{id}$, that adjoint morphism is already the
identity; uniqueness under the adjunction proves the last assertion.
