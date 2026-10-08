+++
id = "sk-prop-nagata-sketch-key-disjointness"
kind = "section"
title = "Improved comparison and key disjointness"
order = 270
uses = ["sk-lem-nagata-sketch-image-transform", "sk-lem-nagata-sketch-near-closure", "sk-prop-nagata-sketch-prepared"]
lean = ["AlgebraicGeometry.exists_prepared_keyDisjoint_twoOpenSide"]
+++
*Proposition (sketch).*

For prepared sides, set

$$
V_{12}=V_1\times_UV_2,\qquad
X_{12}=\SIm(V_{12}\longrightarrow X_1\times_SX_2).
$$

After a further $V_1$-admissible blow-up, the proper projection
$p_1:X_{12}\to X_1$ is an isomorphism near $B_{1,2}$, and

$$
X_{12}\cap(B_{1,2}\times_SB_{2,1})=\varnothing.
$$

## Proof

The restriction $p_1^{-1}(V_1)=V_{12}\to V_1$ is the base change of
$\psi_2$. It is therefore an isomorphism near $Z_{1,2}$, because
$Z_2\subseteq U_2$. Apply [sk-lem-nagata-sketch-near-closure],
using [sk-lem-nagata-sketch-image-transform] to identify the new
comparison space. Now the inverse image of $Z_{1,2}$ is dense in
$p_1^{-1}(B_{1,2})$ and maps under $p_2$ into $Z_{2,2}$.
Thus all of $p_1^{-1}(B_{1,2})$ maps into $B_{2,2}$, which is
disjoint from $B_{2,1}$. This proves the displayed relation.

Uses: [sk-lem-nagata-sketch-image-transform], [sk-lem-nagata-sketch-near-closure], [sk-prop-nagata-sketch-prepared]
