+++
id = "lemma-nagata-relative-affine-space-open-immersion"
kind = "lemma"
title = "The standard affine chart in relative projective space"
order = 310
lean = ["AlgebraicGeometry.AffineSpace.isOpenImmersion_toRelativeProjectiveSpace"]
uses = ["def-nagata-affine-proj", "def-nagata-homogeneous-localization-degree-zero", "def-nagata-projective-space-base-change", "def-nagata-relative-affine-space", "def-nagata-relative-projective-space", "lemma-nagata-relative-affine-space-charts", "lemma-nagata-relative-proj-exists"]
+++
For every $n$ and $S$, the map induced by
$T_i\mapsto T_i/T_0$ identifies $\mathbb A^n_S$ with the standard open
$D_+(T_0)\subseteq\mathbb P^n_S$. In particular it is an open immersion
over $S$ and is compatible with base change.

## Proof

On $V=\operatorname{Spec}(R)$, the degree-zero part of
$R[T_0,\ldots,T_n]_{T_0}$ is the polynomial ring
$R[T_1/T_0,\ldots,T_n/T_0]$. Thus the affine chart is canonically
$\operatorname{Spec}(R[T_1,\ldots,T_n])$. These identifications commute
with localization in $R$, so they glue by
[lemma-nagata-relative-affine-space-charts]; the relative-Proj
restriction isomorphisms from
[lemma-nagata-relative-proj-exists] identify the glued target with
$D_+(T_0)$. Standard Proj charts are open, proving the assertion.
