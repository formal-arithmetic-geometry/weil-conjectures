+++
id = "lem-mg-exterior-direct-sum"
kind = "lemma"
title = "Exterior power of a direct sum"
order = 2547
uses = ["def-wf-weil-category"]
+++
Let $V_1,\ldots,V_s$ be finite-dimensional Weil
representations. For every $N$, there is a canonical Weil-equivariant
decomposition

$$
\bigwedge\nolimits^{N}\!\left(\bigoplus_{i=1}^{s}V_i\right)
\simeq
\bigoplus_{\substack{n_1+\cdots+n_s=N\\ n_i\ge0}}
\bigotimes_{i=1}^{s}\bigwedge\nolimits^{n_i}V_i,
$$

where terms with $n_i>\dim V_i$ are zero.

## Proof

For the Weil representations of [def-wf-weil-category], the map
sends a wedge of vectors to the sum of the terms obtained by
grouping its vectors according to the summand $V_i$, with the induced
signs from reordering. A basis adapted to the direct sum shows that these
terms form a direct sum and span every basis wedge. Since every Weil
operator preserves each $V_i$, the map commutes with the Weil action.
