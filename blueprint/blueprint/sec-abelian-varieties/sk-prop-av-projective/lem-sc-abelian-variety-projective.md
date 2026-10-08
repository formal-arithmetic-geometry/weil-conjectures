+++
id = "lem-sc-abelian-variety-projective"
kind = "lemma"
title = "Abelian varieties are projective"
lean = ["AlgebraicGeometry.IsAbelianScheme.exists_isClosedImmersion_projectiveSpace", "AlgebraicGeometry.IsAbelianScheme.exists_isAmple"]
order = 474
uses = ["def-sc-abelian-variety"]
+++
Every abelian variety $A$ over
a field $k$ is projective over $k$; in particular $A$ carries
an ample invertible $\mathcal O_A$-module.

## Proof

*Reference: Stacks Project, Groupoid Schemes, Lemma 39.9.2,
[Tag 0BFA](https://stacks.math.columbia.edu/tag/0BFA).* The proof of loc. cit. runs as follows.
Every algebraic group scheme over a field is quasi-projective over
$k$ (Groupoid Schemes, Lemma 39.8.7,
[Tag 0BF7](https://stacks.math.columbia.edu/tag/0BF7)), and a
quasi-projective proper scheme over a field is projective (More on
Morphisms, Lemma 37.50.1 (3),
[Tag 0B45](https://stacks.math.columbia.edu/tag/0B45), applied
with $S=\operatorname{Spec}k$, which has an ample invertible
sheaf). Since $A$ is proper, $A$ is projective, and a
projective scheme over a field carries an ample invertible module,
namely the pullback of $\mathcal O(1)$.
