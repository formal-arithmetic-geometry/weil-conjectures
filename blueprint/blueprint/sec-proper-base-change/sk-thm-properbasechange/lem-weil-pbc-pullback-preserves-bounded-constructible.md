+++
id = "lem-weil-pbc-pullback-preserves-bounded-constructible"
kind = "lemma"
title = "Pullback preserves bounded constructibility"
order = 1303
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-constructible-direct-image-finiteness", "def-weil-pbc-proetale-operations", "lem-weil-pbc-comparison-pullback", "prop-weil-pbc-inverse-image-exact"]
+++
Let $\Lambda=P_n$ be as in
[def-weil-pbc-constructible-direct-image-finiteness] and let $g:V'\to V$ be
a morphism of schemes. The derived pullback $Lg^*=g^{-1}$ restricts to an
exact triangulated functor
$$
 Lg^*:\Dbc(V_{\Proet},\Lambda)\longrightarrow\Dbc(V'_{\Proet},\Lambda),
$$
and carries the class of objects with cohomology in $[a,b]$ into the same
class.

*Source note:* no Stacks Project entry states this form. Stacks' nearest
entries are the equivalence defined by $\epsilon^{-1}$ between constructible
sheaves on $X_{\Et}$ and on $X_{\Proet}$, Lemma 61.27.2 ([Tag
09AK](https://stacks.math.columbia.edu/tag/09AK)), its complex-level form
for bounded below complexes, Lemma 61.27.4 ([Tag
09AL](https://stacks.math.columbia.edu/tag/09AL)), and the weak Serre
property of the constructible category, Lemma 61.27.3 ([Tag
09B5](https://stacks.math.columbia.edu/tag/09B5)); the constructibility
entries Definition 61.29.1 ([Tag
09C1](https://stacks.math.columbia.edu/tag/09C1)) and Proposition 61.29.7
([Tag 09C7](https://stacks.math.columbia.edu/tag/09C7)) are stated for a
Noetherian scheme and a Noetherian coefficient ring and concern adic
constructibility, and no entry states that a pullback preserves a
cohomological interval. Difference: the blueprint adds the exactness of
$Lg^*=g^{-1}$ on the finite coefficient rings $P_n$ and the preservation of
the interval $[a,b]$, for the bounded constructible categories of
[def-weil-pbc-constructible-direct-image-finiteness].

## Proof

On the etale site, inverse image is exact and takes a constructible
$\Lambda$-module sheaf to a constructible one: in the partition description
of a constructible complex the restriction to each piece is lisse with
finite stalks, the inverse image of a lisse sheaf is lisse, and the inverse
image of a locally closed constructible subscheme is locally closed
constructible, the preimage of a finite partition being a finite partition.
Hence the bounded constructible etale complexes are preserved, with the
cohomological interval preserved by exactness. For finite constant
coefficients, the pro-etale operations identify the pro-etale inverse image
with the sheaf inverse image, and [lem-weil-pbc-comparison-pullback]
transports the etale statement to the pro-etale site.
