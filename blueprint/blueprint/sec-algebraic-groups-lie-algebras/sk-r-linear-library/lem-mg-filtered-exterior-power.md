+++
id = "lem-mg-filtered-exterior-power"
kind = "lemma"
title = "Exterior power of a filtered representation"
order = 2546
uses = ["def-mg-weil-composition-series"]
+++
Let $0=V_0\subsetneq\cdots\subsetneq V_t=V$ be a
composition series,
put $A_i=V_i/V_{i-1}$ and $d_i=\dim A_i$, and fix
$0\le r\le\dim V$. The Weil representation $\bigwedge^rV$ has a
finite filtration whose nonzero successive quotients are

$$
\bigotimes_{i=1}^{t}\bigwedge\nolimits^{n_i}A_i,
\qquad
0\le n_i\le d_i,
\qquad
\sum_i n_i=r.
$$

Every admissible tuple $(n_1,\ldots,n_t)$ occurs once.

## Proof

Choose, for each $i$, vectors in $V_i$ lifting a basis of $A_i$.
Together these vectors form a basis of $V$ adapted to the filtration in
[def-mg-weil-composition-series]. A basis wedge in
$\bigwedge^rV$ then has a well-defined tuple $(n_i)$, where $n_i$
counts the chosen vectors that lift $A_i$. Relative to the adapted
basis, every Weil-group matrix is block upper triangular: the image of a
lift from $A_i$ is its induced $A_i$-image plus vectors in
$V_{i-1}$. Hence acting on a basis wedge either preserves its tuple or
replaces one index $i$ by a smaller index.

Order the finitely many tuples by any total order extending these lowering
moves, and let the filtration term be the span of all basis wedges whose
tuples occur up to a given place. The preceding triangularity shows that
these spans are Weil-stable. Modulo the earlier tuples, only the diagonal
block actions remain. Sending a wedge of the chosen lifts to the tensor
of its wedges in the separate quotients gives the corresponding quotient

$$
\bigotimes_i\bigwedge^{n_i}A_i.
$$

It is nonzero exactly when $0\le n_i\le d_i$, and every basis wedge has
exactly one tuple, which proves both the list and its multiplicity-one
assertion.
