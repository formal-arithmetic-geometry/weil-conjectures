+++
id = "lem-pd-morphisms-descend"
kind = "lemma"
title = "Morphisms, and hence the group law, descend"
order = 865
uses = ["def-pc-base-change", "def-pd-descent-datum"]
+++
Let $X\to Y$ be a morphism of schemes and let $V\to X$, $W\to X$ be schemes
with descent data over $X/Y$ which are
effective, with descended schemes $V_0,W_0$ over $Y$. Then every morphism
$\psi:V\to W$ over $X$ which is compatible with the two descent data descends
to a unique morphism $\psi_0:V_0\to W_0$ over $Y$.

## Proof

The functor from schemes over $Y$ to schemes over $X$ equipped with a
[def-pd-descent-datum] is fully faithful, by Stacks Project, Descent,
Lemma 35.35.11, Tag
[02W0](https://stacks.math.columbia.edu/tag/02W0); the essential image of
that functor consists of the effective data, the passage from a scheme over
$Y$ to a scheme over $X$ being the base change of
[def-pc-base-change]. Full faithfulness says exactly that a compatible
morphism $\psi$, which is a morphism between two objects in
the essential image, is the base change of a unique $\psi_0$ over $Y$. The
full faithfulness also shows that the descent data on $V$ and $W$ are
determined by $V_0$ and $W_0$, so no choice is involved.
