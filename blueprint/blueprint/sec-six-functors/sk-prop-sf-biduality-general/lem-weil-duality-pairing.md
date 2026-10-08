+++
id = "lem-weil-duality-pairing"
kind = "lemma"
title = "The duality pairing and the double-dual morphism"
order = 2122
uses = ["def-weil-derived-pullback-tensor-hom", "lem-sf-hom-triangulated", "thm-amb-etale-exceptional-adjoint"]
+++
Let $X$ be a separated finite-type scheme over a field, with finite
coefficients invertible on that field. On the ambient etale derived
category put $\omega_X=Ra_X^{\times}A$, using the right adjoint of
[thm-amb-etale-exceptional-adjoint], and let
$D_X=R\mathcal Hom_A(-,\omega_X)$. For every complex $K$, the
evaluation of internal Hom is a natural pairing

$$
\mathrm{ev}_K:D_XK\otimes_A^LK\longrightarrow\omega_X.
$$

Its transpose is the natural double-dual morphism
$\delta_K:K\to D_XD_XK$. It is compatible with shifts and is a
morphism of distinguished triangles. The same formal construction
applies on the pro-etale site whenever its ambient dualizing object is
specified; it does not assume that $D_XK$ is constructible.

## Proof

The tensor–internal-Hom adjunction of
[def-weil-derived-pullback-tensor-hom] has evaluation as its
counit. Compose that evaluation with tensor symmetry, and transpose
under the same adjunction, obtaining $\delta_K$. Naturality of the
counit gives naturality of this map. Internal Hom is triangulated in
each variable, with the standard shift and Koszul-sign conventions, by
[lem-sf-hom-triangulated] (on the pro-etale site by the same Hom-complex
argument);
the natural transformation to its double application therefore
commutes with shifts and gives a morphism of triangles. This
construction takes place in the ambient categories, before any
preservation assertion.
