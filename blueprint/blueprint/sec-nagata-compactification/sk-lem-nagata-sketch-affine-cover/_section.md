+++
id = "sk-lem-nagata-sketch-affine-cover"
kind = "section"
title = "Affine starting pieces and dense overlaps"
order = 306
uses = ["sk-lem-nagata-sketch-closure", "sk-prop-nagata-sketch-zmt"]
lean = ["AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter_spec", "AlgebraicGeometry.HasCompactification.of_isQuasiAffine"]
+++
*Lemma (sketch).*

For a Noetherian $S$ and a separated finite-type $X\to S$, there is
a finite affine open cover $X=\bigcup_{i=1}^n U_i$ with dense total
intersection. Each $U_i\to S$ is compactifiable.

## Proof

A point of a quasi-separated scheme and finitely many generic points
of irreducible components lie in an affine open (01ZX).
Apply this to all generic points of the Noetherian scheme $X$ and
choose a finite subcover. Every $U_i$ contains those generic points,
so their total intersection is dense. An immersion
$U_i\to\mathbb A^{n_i}_S\hookrightarrow\mathbb P^{n_i}_S$ exists by
[sk-prop-nagata-sketch-zmt](ii), $U_i$ being affine, hence a
quasi-affine scheme; its scheme-theoretic image is a
compactification by [sk-lem-nagata-sketch-closure].

Uses: [sk-lem-nagata-sketch-closure], [sk-prop-nagata-sketch-zmt]
