+++
id = "prop-nagata-affine-compactification"
kind = "theorem"
title = "Property of the affine compactification construction"
order = 312
lean = ["AlgebraicGeometry.HasCompactification.of_isQuasiAffine"]
tags = ["latex:proposition"]
uses = ["def-nagata-affine-compactification", "def-nagata-compactifiable", "def-nagata-compactification", "def-nagata-relative-affine-space", "lemma-nagata-affine-finite-type-is-quasi-affine", "lemma-nagata-immersion-into-proper", "lemma-nagata-projective-space-base-change-proper", "lemma-nagata-quasi-affine-immersion-affine-space", "lemma-nagata-quasi-affine-immersion-affine-space-exists", "lemma-nagata-relative-affine-space-open-immersion"]
+++
The constructed factorization $\mathsf C_{\mathrm{aff}}(U/S)$ is a
compactification of $U\to S$. Consequently, if $U$ is a quasi-affine
scheme and $U\to S$ is quasi-compact and locally of finite type, then
$U\to S$ is compactifiable; this applies in particular when $U$ is affine.

## Proof

Since $U$ is affine, it is quasi-affine by
[lemma-nagata-affine-finite-type-is-quasi-affine]. Apply
[lemma-nagata-quasi-affine-immersion-affine-space] to obtain an
immersion $\iota_U\colon U\to\mathbb A^n_S$. Its composite with the
standard open immersion of
[lemma-nagata-relative-affine-space-open-immersion] is an immersion
$U\to\mathbb P^n_S$. By
[lemma-nagata-projective-space-base-change-proper], $\mathbb P^n_S\to S$ is proper.
The immersion-into-proper construction of
[lemma-nagata-immersion-into-proper] therefore supplies a
compactification, and this is exactly
$\mathsf C_{\mathrm{aff}}(U/S)$ by definition.
