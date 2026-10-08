+++
id = "thm-pd-effective-descent"
kind = "theorem"
title = "Effective descent for quasi-projective schemes"
order = 864
uses = ["cor-pd-finite-level", "def-pc-finite-locally-free", "def-pc-morphism-conventions", "def-pc-projective-morphism", "def-pd-descent-datum"]
+++
Let $X\to Y$ be a surjective
finite locally free morphism and let $V$
be a scheme over $X$ such that $V\to X$ is
projective. Then every
descent datum on $V$ over $X/Y$ is effective.
This is Stacks Project, Groupoid Schemes, Lemma 39.25.3, Tag
[0CCJ](https://stacks.math.columbia.edu/tag/0CCJ).

## Proof

This is Stacks Project, Groupoid Schemes, Lemma 39.25.3, Tag
[0CCJ](https://stacks.math.columbia.edu/tag/0CCJ). In the notation of
[def-pd-descent-datum] and [def-pc-morphism-conventions] we recall
why projectivity ([def-pc-projective-morphism]) is exactly the hypothesis
that makes the descent effective, since that is the point at which the
projectivity of $J_K$ of [cor-pd-finite-level] is used. In loc. cit. the effectiveness is deduced from Lemma 39.25.2, Tag
[0CCI](https://stacks.math.columbia.edu/tag/0CCI), which states that a
descent datum on $V/X/Y$ is effective as soon as every finite set of points of
$V$ lying over one point of $Y$ is contained in an affine open of $V$; that
criterion in turn is Lemma 39.25.1, Tag
[0H8K](https://stacks.math.columbia.edu/tag/0H8K), proved by producing a
$\varphi$-invariant affine open neighbourhood of each point (Constructions,
Lemma 27.2.1, Tag [01LH](https://stacks.math.columbia.edu/tag/01LH), for
the reduction to $Y$ affine, and Lemma 39.24.1, Tag
[03JE](https://stacks.math.columbia.edu/tag/03JE), for the invariant
neighbourhood) and glueing along the resulting covering. A projective $V\to X$ has an $X$-very ample invertible sheaf, and for an ample invertible sheaf
finitely many points lie in an affine open (Properties, Lemma 28.30.5, Tag
[01ZY](https://stacks.math.columbia.edu/tag/01ZY)), which is the
condition of Lemma 39.25.2; this is the verification carried out in the proof
of Stacks Project, Lemma 39.25.3, Tag
[0CCJ](https://stacks.math.columbia.edu/tag/0CCJ), cases (1), (2) and
(4). The hypothesis that $X\to Y$ be
[def-pc-finite-locally-free] is what makes the fibres of the two
projections finite and hence the orbits of Lemma 39.25.1 finite.
