+++
id = "lem-weil-pbc-finite-pushforward-constructible-noetherian"
kind = "lemma"
title = "Finite pushforward preserves constructibility on Noetherian schemes"
order = 1579
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-etale-sheaves", "def-weil-pbc-scheme-conventions", "lem-weil-pbc-finite-pushforward-generic-constructible", "lem-weil-pbc-noetherian-finite-components", "lemma-weil-pbc-finite-exchange"]
+++
Let $U$ be Noetherian, let $h:V\to U$ be finite, and let $E$ be a
constructible abelian etale sheaf on $V$. Then its direct image $h_*E$ is
constructible on $U$.

## Proof

Pullback preserves constructibility: pull back the finite locally closed
partition and each of its finite constant etale trivializations. For every
closed subset $T\subset U$, give $T$ its reduced scheme structure and put
$V_T=V\times_UT$. [lemma-weil-pbc-finite-exchange] identifies $(h_*E)|_T$ with
the direct image of the constructible pullback of $E$ along the finite map
$V_T\to T$.

We prove that $(h_*E)|_T$ has a finite lisse partition by Noetherian
induction on these closed subsets. The empty subset is immediate. If $T$ is
reducible, its finitely many irreducible components $T_1,\ldots,T_r$ from
[lem-weil-pbc-noetherian-finite-components] are proper closed subsets. Apply
induction to each and restrict its partition to
$T_i\setminus\bigcup_{j<i}T_j$. These restricted pieces are locally closed,
disjoint and cover $T$.

If $T$ is irreducible, its reduced structure is integral. Choose a nonempty
affine open $Q\subset T$ and apply
[lem-weil-pbc-finite-pushforward-generic-constructible] to $V_Q\to Q$. It
supplies a dense open $Q^\circ\subset T$ on which $(h_*E)|_T$ is lisse. The
proper closed complement $T\setminus Q^\circ$ has a finite lisse partition by
induction. Adjoining $Q^\circ$ gives the required partition of $T$. At
$T=U_{\mathrm{red}}$, its locally closed pieces, composed with
$U_{\mathrm{red}}\to U$, are locally closed subschemes partitioning $U$, which
proves constructibility on $U$. No finite bound on the Krull dimension is
used.
