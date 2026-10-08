+++
id = "lem-kun-03sa"
kind = "lemma"
title = "Constructible generation"
order = 1772
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "thm-constructible-serre"]
+++
Let $X$ be a scheme of
finite type over a field and
$\Lambda$ a finite commutative ring. A sheaf of $\Lambda$-modules on
$X_{\Et}$ is a filtered colimit of
constructible
$\Lambda$-module sheaves.
(*Source:* Stacks Project,
[Lemma 59.73.2, Tag
`03SA`](https://stacks.math.columbia.edu/tag/03SA), stated there for quasi-compact and quasi-separated
schemes, the finite-type case being the one used here.) In the Stacks Project the proof uses Modules on Sites, Lemma 18.30.7,
[Tag `093C`](https://stacks.math.columbia.edu/tag/093C)
(every sheaf of modules is a filtered colimit of cokernels of maps
between finite direct sums of the sheaves $j_{U!}\Lambda_U$ for $U$
in a basis), together with Lemma 59.73.1,
[Tag `03S8`](https://stacks.math.columbia.edu/tag/03S8)
(those cokernels are constructible); the weak-Serre property used there,
Lemma 59.71.6, [Tag
`03RZ`](https://stacks.math.columbia.edu/tag/03RZ), is proved in this chapter as [thm-constructible-serre].

## Proof

This is the recorded classical input named in the statement, Stacks Project, Lemma 59.73.2 ([Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)): on a quasi-compact and quasi-separated scheme, every sheaf of modules is a filtered colimit of constructible sheaves; the case used here is that of a scheme of finite type over a field. In the Stacks Project the proof uses Modules on Sites, Lemma 18.30.7 ([Tag 093C](https://stacks.math.columbia.edu/tag/093C)) together with Lemma 59.73.1 ([Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)), the weak-Serre property used there being proved in this chapter as [thm-constructible-serre]. No separate proof is given.
