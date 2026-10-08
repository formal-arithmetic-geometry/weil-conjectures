+++
id = "sbc-prop-extension-by-zero-and-arbitrary-base-change"
kind = "theorem"
title = "Extension by zero base change"
order = 1434
tags = ["latex:proposition"]
uses = ["def-weil-pbc-extension-by-zero", "def-weil-pbc-scheme-conventions"]
+++
For an open immersion $j:U\hookrightarrow Z$ of
schemes and a Cartesian
square with base change $a:Z'\to Z$, extension by zero
([def-weil-pbc-extension-by-zero]) is exact and

$$
a^{-1}j_!F\xrightarrow{\ \sim\ }j'_!a_U^{-1}F
$$

for every sheaf $F$ on $U_{\Et}$, and the same holds for complexes.
(*Stacks Project, Etale Cohomology, Lemma 59.70.5, [Tag `03S6`](https://stacks.math.columbia.edu/tag/03S6).*)

## Proof

Extension by zero is computed sectionwise as in
[def-weil-pbc-extension-by-zero]: for etale $V\to Z'$ the sections
of $j'_!a_U^{-1}F$ over $V$ are the sections of $a_U^{-1}F$ over
$V\times_{Z'}U'$, i.e. over $V\times_ZU$, while
$(a^{-1}j_!F)(V)=j_!F(V\times_ZZ_V)$ has the same description; the
Cartesian identification gives the natural isomorphism, and for
complexes the same argument applies termwise.
