+++
id = "sbc-lem-degree-zero-flat-base-change"
kind = "lemma"
title = "Degree-zero flat base change"
order = 1382
uses = ["def-sbc-normal-dominant-galois", "def-weil-pbc-direct-image", "sbc-def-base-change-square"]
+++
Consider a base-change square
where $f$ is flat and locally of finite presentation with
geometrically reduced
fibres (in particular, $f$ may be smooth). Then

$$
f^{-1}g_*\mathcal F=h_*e^{-1}\mathcal F
$$

for any sheaf $\mathcal F$ on $T_{\Et}$.
(*Stacks Project, Etale Cohomology, Section 59.87 (Base change
for pushforward), [Tag `0EYS`](https://stacks.math.columbia.edu/tag/0EYS) = Lemma 59.87.2; the proof combines
Lemma 59.87.1, [Tag `0EZX`](https://stacks.math.columbia.edu/tag/0EZX), with More on Morphisms, Lemma
37.46.3, [Tag `0EY5`](https://stacks.math.columbia.edu/tag/0EY5): the connected components of the fibres
correspond under the base change, and direct image is computed by the
would-be equalizer of the section descriptions.*)

## Proof

The direct image of [def-weil-pbc-direct-image] is computed by the
equalizer description of sections along the fibres; for a flat
morphism of finite presentation with geometrically reduced fibres, the
(reduced) connected components of the fibres are the geometric points,
and they correspond under base change, so for $V\to T$ etale the
sections of both sides over $V$ are the same systems of sections on the
fibres of $V\times_TY\to V$: this identifies $f^{-1}g_*\mathcal F$ and
$h_*e^{-1}\mathcal F$ as sheaves, which is the displayed equality.
