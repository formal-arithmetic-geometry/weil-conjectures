+++
id = "lem-mg-filtered-tensor-product"
kind = "lemma"
title = "Tensor product of two filtered representations"
order = 2545
uses = ["def-mg-weil-composition-series"]
+++
Let $V_\bullet$ and $W_\bullet$ be
composition series, and put
$A_i=V_i/V_{i-1}$ and $B_j=W_j/W_{j-1}$. The Weil representation
$V\otimes W$ has a finite filtration whose successive quotients, in a
suitable order, are

$$
A_i\otimes B_j\qquad(1\le i\le t,\ 1\le j\le u).
$$

Every pair $(i,j)$ occurs exactly once in this displayed list of
successive quotients.

## Proof

First filter $V\otimes W$ by the subspaces $V_i\otimes W$. Tensoring
vector spaces over a field is exact, so

$$
(V_i\otimes W)/(V_{i-1}\otimes W)\simeq A_i\otimes W.
$$

Inside this quotient use the filtration
$A_i\otimes W_0\subseteq\cdots\subseteq A_i\otimes W_u$, whose
successive quotients are $A_i\otimes B_j$. Pull these subspaces back to
$V_i\otimes W$, and do this successively for $i=1,\ldots,t$. All
maps are Weil-equivariant because both series in
[def-mg-weil-composition-series] consist of Weil-stable subspaces.
The resulting concatenated filtration has precisely the asserted
quotients.
