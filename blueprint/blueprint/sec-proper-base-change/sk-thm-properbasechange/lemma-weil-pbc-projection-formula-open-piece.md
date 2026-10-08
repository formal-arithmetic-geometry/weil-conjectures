+++
id = "lemma-weil-pbc-projection-formula-open-piece"
kind = "lemma"
title = "Open-immersion tensor piece"
order = 1269
uses = ["def-weil-pbc-projection-compactification"]
+++
For a bounded finite-projective complex $F^\bullet$ on $\overline X$, the
canonical map

$$
(j_!E)\otimes^LF^\bullet
\xrightarrow{\sim}j_!(E\otimes^LLj^*F^\bullet)
$$

is an isomorphism, natural in $E$ and $F^\bullet$.

## Proof

Extension by zero along an open immersion is exact. Resolve only $E$;
tensoring with each finite projective term remains exact. At a point of the
pro-etale topos lying over $X$, both sides are $E_x\otimes F_x^\bullet$ and
the map is the identity. At a point lying over
$\overline X\setminus X$, both sides are zero. These points form a
conservative family, so the term map is an isomorphism. It commutes with
$d_F$ and with the signed total differential, hence gives the displayed
derived isomorphism.
