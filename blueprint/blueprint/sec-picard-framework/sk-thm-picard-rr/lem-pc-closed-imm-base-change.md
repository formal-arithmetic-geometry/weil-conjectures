+++
id = "lem-pc-closed-imm-base-change"
kind = "lemma"
title = "The ideal sheaf of a base-changed closed immersion"
order = 726
uses = ["def-pc-scheme"]
+++
(Schemes, Lemma 26.18.2, Tag
[01JY](https://stacks.math.columbia.edu/tag/01JY).) Closed immersions
are stable under arbitrary base change; if $i:Z\to X$ is a closed
immersion with ideal sheaf $\mathcal{I}_Z$, and $g:X'\to X$ is a morphism, then
$Z'=Z\times_XX'$ is a closed subscheme of $X'$ whose ideal sheaf is the
pullback $g^*\mathcal{I}_Z$; in particular for a closed immersion with a section
structure this yields the canonical identification $\mathcal{I}_{x_K}=\mathcal{I}_x\otimes \mathcal{O}_{X_K}$ for $\kappa(x)$-points.

## Proof

The first assertion is the statement that closed immersions are stable
under base change (Schemes, Lemma 26.18.2, Tag
[01JY](https://stacks.math.columbia.edu/tag/01JY)): the pullback
$Z\times_XX'\to X'$ is a closed immersion; for the ideal sheaf, the
pullback $g^*\mathcal{I}_Z$ is the ideal sheaf of the base change: the
exactness argument: $g^*$ is right exact, so applying it to the exact
sequence $0\to\mathcal{I}_Z\to\mathcal{O}_X\to i_*\mathcal{O}_Z\to0$ gives an exact sequence
$g^*\mathcal{I}_Z\to\mathcal{O}_{X'}\to g^*i_*\mathcal{O}_Z\to0$; the last map is the canonical
$\mathcal{O}_{X'}\to i'_*\mathcal{O}_{Z'}$, the image of $g^*\mathcal{I}_Z$ in $\mathcal{O}_{X'}$ is therefore
its kernel, i.e. the ideal sheaf of $Z'$ (the base change of the closed
immersion is the closed immersion with this ideal sheaf, by the affine
computation: on affines, $A\to A/I$ and $B=A'$-tensored: the ideal of
$Z'$ is $(A'\otimes_A I)$-image = the kernel of
$A'\to A'\otimes_AA/I$). This gives
$\mathcal{I}_{Z'}=g^*\mathcal{I}_Z$.
