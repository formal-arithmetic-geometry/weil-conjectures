+++
id = "lem-pc-genus-agrees-sc"
kind = "lemma"
title = "Agreement with the genus of file 06"
order = 811
uses = ["def-pc-genus", "def-pc-smooth-projective-curve", "def-sc-curves", "def-sc-genus"]
+++
Let $k$ be an algebraically closed field and $C$ a
smooth projective curve over
$k$ (or, more generally, a proper smooth connected curve in the sense of
[def-sc-curves] with $\dim H^0(C,\mathcal{O}_C)=1$). Then the genus
$g(C)$ of [def-pc-genus] equals the genus of
[def-sc-genus].

## Proof

Both definitions are $g=\dim_kH^1(C,\mathcal{O}_C)$ (Definition 44.6.3 in the
first case, specific to the geometric irreducible smooth projective
curve; Definition 53.8.1 (Tag
[0BY7](https://stacks.math.columbia.edu/tag/0BY7)) in the second),
so they agree.
