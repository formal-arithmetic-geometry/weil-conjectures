+++
id = "lem-weil-pbc-irreducible-lisse-strata"
kind = "lemma"
title = "Irreducible lisse strata"
order = 1602
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-noetherian-finite-components"]
+++
Let $X$ be Noetherian and $F$ a constructible abelian etale sheaf on $X$.
There is a finite partition $X=\coprod_{i=1}^m S_i$ into nonempty irreducible
locally closed subschemes such that each $F|_{S_i}$ is locally constant with
finite stalks.

## Proof

Start with the finite lisse partition supplied by constructibility. A part $S$
is Noetherian, so [lem-weil-pbc-noetherian-finite-components] lists its
irreducible components as $C_1,\ldots,C_r$. Put

$$
 S_i=C_i\setminus\bigcup_{j<i}C_j.
$$

Each $S_i$ is open in $C_i$, and contains its generic point: an irreducible
component is not contained in the union of the other finitely many
components. Thus $S_i$ is nonempty and irreducible. These sets are disjoint
and cover $S$; they are locally closed in $S$, hence in $X$. Give them their
reduced locally closed scheme structures. Restriction of an etale
trivialization shows that $F|_{S_i}$ is still locally constant with finite
stalks. Performing this construction for the finitely many original parts
gives the required partition.
