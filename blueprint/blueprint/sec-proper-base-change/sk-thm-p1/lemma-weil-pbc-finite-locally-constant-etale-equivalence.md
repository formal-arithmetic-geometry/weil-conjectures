+++
id = "lemma-weil-pbc-finite-locally-constant-etale-equivalence"
kind = "lemma"
title = "Finite locally constant sheaves and finite-etale schemes"
order = 1123
+++
For a scheme $T$, finite locally constant sheaves of sets on $T_{\mathrm{et}}$
are equivalent to finite etale $T$-schemes. A finite abelian group action on
the sheaf corresponds to an action by finite-etale $T$-automorphisms.

## Proof

Given a sheaf $E$, choose a finite etale cover $U\to T$ trivializing it with
finite fibre $S$. The descent isomorphism on $U\times_TU$ is a permutation
of $S$ satisfying the cocycle equation, hence descends the disjoint union
$\coprod_{s\in S}U$ to a finite etale scheme $P$. Conversely, the sheaf of
sections of a finite etale $P$ is finite locally constant; the two constructions
are inverse because both are computed after the same trivializing cover.
An $M$-action is a compatible family of permutations, so it descends exactly
when the sheaf action is compatible with the descent cocycle.
