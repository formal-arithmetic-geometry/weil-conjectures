+++
id = "fin2-lem-lisse-dense-open"
kind = "lemma"
title = "A lisse locus for a constructible sheaf"
order = 2666
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-noetherian-finite-components"]
+++
Let $X$ be of finite type over $k$ and let $F$ be a
constructible
$\Lambda$-sheaf on $X_{{\mathrm{et}}}$. Then there is an open
subscheme $U\hookrightarrow X$ with
$\dim(X\setminus U)<\dim X$ on which the restriction $F|_U$ is
lisse.

## Proof

If $X$ is empty, take $U=X$.
Otherwise let $C_1,\ldots,C_t$ be all its irreducible components,
using [lem-weil-pbc-noetherian-finite-components].
For each component of maximal dimension, first remove all other
components. This gives an irreducible open $O_i$ of $X$
containing its generic point $\eta_i$. By the finite partition
in [def-weil-pbc-constructible-complexes], the stratum containing
$\eta_i$ contains a nonempty open $V_i\subset O_i$.
The restriction to $V_i$ is finite locally constant.
The $V_i$ are disjoint opens of $X$, so their finite union $U$
is open and $F|_U$ is finite locally constant.
The closed complement meets every maximal-dimensional component in
a proper closed subset. For finite-type schemes over a field such
a subset has strictly smaller dimension, by the dimension formula
for finitely generated algebras. The other components already have
smaller dimension. Hence $\dim(X\setminus U)<\dim X$.
