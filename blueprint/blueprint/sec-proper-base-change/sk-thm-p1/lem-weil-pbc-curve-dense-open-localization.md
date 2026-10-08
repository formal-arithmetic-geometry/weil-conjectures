+++
id = "lem-weil-pbc-curve-dense-open-localization"
kind = "lemma"
title = "Dense-open localization"
order = 1171
uses = ["def-constructible-constructible", "def-constructible-stratification", "def-weil-pbc-curve-setting", "def-weil-pbc-eight-curve-assertions", "def-weil-pbc-etale-sheaves", "lem-weil-pbc-zero-dimensional-cohomology", "lem-weil-pbc-zero-dimensional-field-extension", "lemma-weil-pbc-eight-curve-devissage", "prop-constructible-generic-constancy", "prop-weil-pbc-geometric-stalks-exact"]
+++
Let $C$ be a reduced curve and $F$ a constructible $\mathbf F_r$-sheaf. There
is a dense open $j:U\hookrightarrow C$, a finite disjoint union of irreducible
curves, on which $F$ is finite locally constant. For $i:Z=C\setminus
U\hookrightarrow C$ there is a natural exact sequence

$$
 0\to j_!j^{-1}F\to F\to i_*i^{-1}F\to0,
$$

and $Z$ is zero-dimensional. Write $U=\coprod_aU_a$ and let
$j_a:U_a\hookrightarrow C$ be the composite open immersion. Then

$$
 \mathcal C(C,F)\quad\Longleftrightarrow\quad
 \mathcal C(C,j_{a,!}(F|_{U_a}))\text{ for every }a.
$$

## Proof

The finite partition of $C$ into locally closed constructible subschemes on
which the constructible $\mathbf F_r$-sheaf $F$ is lisse (locally constant with
finite stalks) is a stratification in the sense of
[def-constructible-stratification] whose pullbacks of $F$ are finite locally
constant, so $F$ is constructible in the sense of
[def-constructible-constructible]. By [prop-constructible-generic-constancy]
there is a dense open $U'\subseteq C$ with $F|_{U'}$ finite locally constant.
Remove from $U'$ the finitely many closed points at which two distinct
irreducible components of $C$ meet; the result is a dense open
$j:U\hookrightarrow C$ on which $F$ is still finite locally constant, a reduced
curve whose irreducible components are disjoint, hence a finite disjoint union
$U=\coprod_aU_a$ of irreducible curves. Its complement $i:Z\hookrightarrow C$
contains no generic point of $C$, so it is zero-dimensional. The sequence
$0\to j_!j^{-1}F\to F\to i_*i^{-1}F\to0$ is exact, since at geometric points
of $U$ the middle and left terms agree and the right term vanishes, and at
geometric points of $Z$ the left term vanishes and the sequence is the
identity of the right term. For the equivalence: $j_!j^{-1}F$ decomposes as
the finite direct sum of the $j_{a,!}(F|_{U_a})$ (the $U_a$ are open and
closed in $U$), the terms $i_*i^{-1}F$ are constructible on the
zero-dimensional $Z$, where all $\mathcal C_j$
([def-weil-pbc-eight-curve-assertions]) hold: the vanishing and
finite-stalk finiteness statements follow from
[lem-weil-pbc-zero-dimensional-cohomology], field-extension invariance follows
from [lem-weil-pbc-zero-dimensional-field-extension], and (C8) is a map
between zero groups. Moreover, $\mathcal C(-,G_1\oplus G_2)$ is equivalent to
$\mathcal C(-,G_1)\wedge\mathcal C(-,G_2)$ for the finite direct sums;
together with [lemma-weil-pbc-eight-curve-devissage] this gives the displayed
equivalence.
