+++
id = "lem-weil-karoubi-envelope-triangulated"
kind = "lemma"
title = "Triangulated Karoubi envelope"
order = 1423
uses = ["def-weil-karoubi-envelope"]
+++
Let $\mathcal T$ be a triangulated category. With the shift
$(K,e)[1]=(K[1],e[1])$ and with distinguished triangles the triangles
isomorphic to direct summands, in the category of triangles, of images of
distinguished triangles of $\mathcal T$, the category $\Kar(\mathcal T)$ of
[def-weil-karoubi-envelope] is an ordinary triangulated category, and the
canonical functor of [def-weil-karoubi-envelope] is exact.

(*Source: the classical Balmer--Schlichting idempotent completion of
triangulated categories; retained here as the auxiliary model used in the
proof of the bounded-t-structure theorem below, after which the envelope is
shown to be redundant; no Stacks Project entry states this form: Stacks' only
entries on idempotents are the definition of a Karoubian preadditive category
(Definition 12.4.1, Tag
[09SG](https://stacks.math.columbia.edu/tag/09SG)), its characterization by
the splitting of idempotents (Lemma 12.4.2, Tag
[09SH](https://stacks.math.columbia.edu/tag/09SH)) and the Karoubianity
criteria of Lemma 12.4.3 (Tag
[05QV](https://stacks.math.columbia.edu/tag/05QV): countable products and
kernels of maps which have a right inverse, or dually countable coproducts
and cokernels of maps which have a left inverse), all in Homological Algebra,
Section 12.4 (Tag [09SF](https://stacks.math.columbia.edu/tag/09SF)); Chapter
13 contains no idempotent completion of a triangulated category, and the
derived-limit and K-injective entries 08TC, 07KC, 0BK6, 0BK7, 070M, 079P
concern a fixed triangulated category rather than its idempotent completion;
the blueprint adds the description of the distinguished triangles of
$\Kar(\mathcal T)$ as retracts of images of distinguished triangles of
$\mathcal T$.*)

## Proof

The assertion is the idempotent-completion input recorded in the source note.
It is not discharged here: it enters the blueprint only through the auxiliary
model $\Kar(\mathcal T)$ of [def-weil-karoubi-envelope] in the
bounded-t-structure theorem below, whose finite-stage and $\Qlb$-stage
conclusions make the envelope redundant for the coefficient categories.
