+++
id = "lem-kun-invertible-orders-colimit"
kind = "lemma"
title = "The colimit description of invertible orders"
order = 1688
uses = ["def-kun-torsion-invertible", "def-weil-pbc-etale-sheaves", "lem-kun-stalks-commute-colimits", "lemma-weil-pbc-geometric-stalk-conservative", "lemma-weil-pbc-torsion-filtered-union"]
+++
Let $K$ be a field and $F$ a
torsion sheaf on the etale site
of a $K$-scheme; write $F[n]=\ker(n:F\to F)$ and let $I_K$ be the
set of integers invertible in $K$, as in
[def-kun-torsion-invertible]. Then $F$ has orders invertible in
$K$ if and only if

$$
F=\varinjlim_{n\in I_K}F[n].
$$

## Proof

Since $F$ is torsion, $F=\varinjlim_{n\ge1}F[n]$ by
[lemma-weil-pbc-torsion-filtered-union], and the canonical map
$\varinjlim_{n\in I_K}F[n]\to F$ is the comparison of the
sub-colimit over the divisibility-ordered subset
$I_K\subseteq\mathbf N_{>0}$. Geometric stalks commute with these
colimits ([lem-kun-stalks-commute-colimits]), so this comparison
is an isomorphism if and only if it is an isomorphism on every
geometric stalk ([lemma-weil-pbc-geometric-stalk-conservative]); on
a stalk it says that every element is killed by some $n\in I_K$,
which is exactly the defining condition of
[def-kun-torsion-invertible]. The notion of a torsion sheaf is
that of [def-weil-pbc-etale-sheaves].
