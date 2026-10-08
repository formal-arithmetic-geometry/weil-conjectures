+++
id = "lem-pc-flat-complex-derived-pullback"
kind = "lemma"
title = "Termwise derived pullback of a bounded above flat complex"
order = 666
uses = ["def-pc-derived-pullback", "def-pc-scheme", "def-weil-derived-tensor"]
+++
Let $g:T\to S$ be a morphism of schemes and let $E$ be a bounded above
complex of flat $\mathcal{O}_S$-modules. Then the derived pullback
$Lg^*E$ of [def-pc-derived-pullback] is represented by the complex
$g^*E$ obtained by pulling $E$ back term by term: the canonical map
$g^*E\to Lg^*E$ is a quasi-isomorphism.

## Proof

By [def-pc-derived-pullback],
$Lg^*E=\mathcal{O}_T\otimes^{\mathbf L}_{g^{-1}\mathcal{O}_S}g^{-1}E$,
and by [def-weil-derived-tensor] this derived tensor product is
computed by a K-flat resolution of $g^{-1}E$. Inverse image along a
morphism of schemes is exact and preserves flatness, so $g^{-1}E$ is a
bounded above complex of flat $g^{-1}\mathcal{O}_S$-modules; a bounded
above complex of flat modules over a ringed space is K-flat (Cohomology
of Sheaves, Lemma 20.26.9, Tag
[06YD](https://stacks.math.columbia.edu/tag/06YD)). Hence
$g^{-1}E$ is a K-flat resolution of itself and

$$
Lg^*E=\mathcal{O}_T\otimes_{g^{-1}\mathcal{O}_S}g^{-1}E=g^*E,
$$

which is the termwise pullback of $E$, as claimed.
