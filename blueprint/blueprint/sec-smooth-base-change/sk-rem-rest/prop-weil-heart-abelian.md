+++
id = "prop-weil-heart-abelian"
kind = "theorem"
title = "The heart is abelian"
order = 1425
uses = ["def-weil-t-structure"]
tags = ["latex:proposition"]
+++
For a t-structure $(\mathcal T^{\le0},\mathcal T^{\ge0})$ on a triangulated
category, the heart $\mathcal T^{\le0}\cap\mathcal T^{\ge0}$ of
[def-weil-t-structure] is abelian. Consequently every idempotent of the heart
splits: an idempotent $e:A\to A$ of an abelian category splits as
$A\cong\ker(e)\oplus\ker(\operatorname{id}_A-e)$, with $e$ carried to the
projection onto the second summand.

(*Source: the classical theorem on t-structures and their hearts in
Beilinson--Bernstein--Deligne; the second assertion is the elementary
abelian-category argument exhibited in the proof; no Stacks Project entry
states this form: Stacks has no heart of a t-structure (it defines no
t-structure at all; see the pages listed at [def-weil-t-structure]) and no
abelian-category statement that idempotents split — the nearest is the
splitting criterion for a Karoubian preadditive category, Lemma 12.4.2 (Tag
[09SH](https://stacks.math.columbia.edu/tag/09SH)) (3) with Definition 12.4.1
(Tag [09SG](https://stacks.math.columbia.edu/tag/09SG)), which presupposes
Karoubianity instead of proving it for an abelian category. The blueprint
adds the explicit supplementary-kernel argument for the splitting of an
idempotent of the heart, which together with the Karoubianity theorem below
replaces any appeal to a Stacks entry.*)

## Proof

For the heart defined in [def-weil-t-structure], the abelianity assertion is
the classical theorem recorded in the source note. Its only use below is that
the heart is idempotent complete: for an idempotent $e$ in an abelian
category the kernels $\ker(e)$ and $\ker(\operatorname{id}_A-e)$ are
supplementary subobjects of $A$, the map
$\ker(e)\oplus\ker(\operatorname{id}_A-e)\to A$ is an isomorphism
($\operatorname{id}_A=e+(\operatorname{id}_A-e)$, and the two kernels have
zero intersection), and under it $e$ becomes the projection onto the second
summand with the canonical maps of the split.
