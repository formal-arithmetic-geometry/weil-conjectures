+++
id = "lem-kun-descent-limit"
kind = "lemma"
title = "A sheaf on an affine inverse limit is a colimit"
order = 1658
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "def-weil-pbc-scheme-conventions", "lem-kun-fp-algebra-descent"]
+++
Let $X=\varprojlim_iX_i$ be a directed inverse limit of affine schemes with
affine transition maps, and write $p_i:X\to X_i$. For every torsion abelian
sheaf $F$ on $X_{\Et}$, the sheaves $p_{i,*}F$, with their
canonical transition maps, form a compatible system and the canonical
morphism

$$
\varinjlim_ip_i^{-1}p_{i,*}F\longrightarrow F
$$

is an isomorphism. (*Source:* Stacks Project,
[Tag
`0EYN`](https://stacks.math.columbia.edu/tag/0EYN).) In the Stacks Project this is a special case of Sites, Lemma 7.18.5,
[Tag `0EXJ`](https://stacks.math.columbia.edu/tag/0EXJ), via
Lemma 59.51.2, [Tag
`0EYL`](https://stacks.math.columbia.edu/tag/0EYL) (the affine etale site of an affine limit is the colimit
of the affine etale sites of the stages). The first step of that reduction,
the descent of finitely presented algebras along the colimit of rings, is proved
in this chapter as [lem-kun-fp-algebra-descent].
The affine and torsion case recorded here is the one used in this chapter.

## Proof

This is the recorded classical input named in the statement, Stacks Project, Tag [0EYN](https://stacks.math.columbia.edu/tag/0EYN): for a directed inverse limit of affine schemes with affine transition maps, a torsion sheaf is the filtered colimit of the inverse images of its pushforwards to the stages. In the Stacks Project this is a special case of Sites, Lemma 7.18.5 ([Tag 0EXJ](https://stacks.math.columbia.edu/tag/0EXJ)) via Lemma 59.51.2 ([Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)); the first step of that reduction is proved in this chapter as [lem-kun-fp-algebra-descent]. No separate proof is given here.
