+++
id = "lem-kun-kflat-criteria"
kind = "lemma"
title = "K-flat criteria"
order = 1713
uses = ["def-kun-derived-tensor", "def-kun-truncations", "def-weil-pbc-etale-sheaves"]
+++
Let $\Lambda$ be a commutative ring and $T$ a scheme, and work on
$T_{\Et}$ with $\Lambda_T$-module sheaves.

1. **(1)** Every bounded-above complex of flat $\Lambda_T$-module
sheaves is K-flat.
1. **(2)** In a distinguished triangle of complexes of
$\Lambda_T$-module sheaves, if two of the three terms are K-flat then
so is the third; in particular cones of maps between K-flat complexes
are K-flat.
1. **(3)** Filtered colimits of K-flat complexes are K-flat; in
particular every bounded-below complex of flat $\Lambda_T$-module
sheaves is K-flat.

## Proof

(1) For a $\Lambda_T$-module sheaf as in
[def-weil-pbc-etale-sheaves] the notion of K-flatness is that of
[def-kun-derived-tensor]. Let $\mathcal F^\bullet$ be a bounded-above complex of flat
sheaves, $\mathcal F^i=0$ for $i>N$, and let
$\mathcal A^\bullet$ be an acyclic complex. By descending induction
on $N$ we show that $\mathcal F^\bullet\otimes_\Lambda\mathcal A^\bullet$ is acyclic. The stupid truncation of
[def-kun-truncations] gives a short exact
sequence of complexes

$$
0\to\mathcal F^N[-N]\to\mathcal F^\bullet\to
\sigma_{\le N-1}\mathcal F^\bullet\to0 ,
$$

and tensoring it with $\mathcal A^\bullet$ preserves exactness
because it is exact degreewise (the terms $\mathcal F^i$ are flat);
the resulting triangle shows that the middle term is acyclic whenever
the outer two are, by the long exact cohomology sequence. Now
$\mathcal F^N[-N]\otimes_\Lambda\mathcal A^\bullet$ is a shift of
$\mathcal F^N\otimes_\Lambda\mathcal A^\bullet$, which is acyclic as
$\mathcal F^N$ is flat, and
$\sigma_{\le N-1}\mathcal F^\bullet\otimes_\Lambda\mathcal A^\bullet$
is acyclic by induction. Hence
$\mathcal F^\bullet\otimes_\Lambda\mathcal A^\bullet$ is acyclic, and
$\mathcal F^\bullet$ is K-flat.
(2) Tensoring a distinguished triangle with the acyclic complex
$\mathcal A^\bullet$ gives a distinguished triangle; if two of its
terms are acyclic then so is the third, by the long exact cohomology
sequence. Hence if two terms of the original triangle are K-flat, the
third is as well. A cone is the third term of the triangle determined
by the map.
(3) Let $\mathcal K^\bullet=\varinjlim_i\mathcal K_i^\bullet$ be a
filtered colimit of K-flat complexes. Filtered colimits of
$\Lambda_T$-module sheaves are exact and commute with tensor products,
and homology commutes with filtered colimits, so for every acyclic
$\mathcal A^\bullet$,

$$
\mathcal K^\bullet\otimes_\Lambda\mathcal A^\bullet
=\varinjlim_i\bigl(\mathcal K_i^\bullet\otimes_\Lambda\mathcal
A^\bullet\bigr)
$$

is a filtered colimit of acyclic complexes, hence acyclic; thus
$\mathcal K^\bullet$ is K-flat. A bounded-below complex
$\mathcal F^\bullet$ of flat sheaves is the filtered colimit of its
stupid truncations $\sigma_{\le n}\mathcal F^\bullet$
([def-kun-truncations]), each of which is bounded, hence
bounded above and flat, hence K-flat by (1).
