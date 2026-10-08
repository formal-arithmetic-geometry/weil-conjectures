+++
id = "lem-wf-affine-noetherian-components"
kind = "lemma"
title = "Affine schemes of finite type are Noetherian with finitely many components"
order = 2483
+++
Let $A$ be a finitely generated commutative algebra over a field $k$ and
$X=\operatorname{Spec}A$. Then $A$ is Noetherian, every descending chain
of closed subsets of $X$ stabilizes, and $X$ has only finitely many
irreducible components.

## Proof

*Noetherianity.* Choose a surjection $k[t_1,\ldots,t_n]\to A$. The
polynomial ring is Noetherian by the Hilbert basis theorem, and a
quotient of a Noetherian ring is Noetherian, because ideals of $A$
correspond to ideals of $k[t_1,\ldots,t_n]$ containing the kernel,
compatibly with inclusions; so $A$ satisfies the ascending chain
condition on ideals.

*Descending chains of closed sets.* Every closed subset of $X$ is
$V(I)$ for an ideal $I$, and $V(I)=V(\sqrt I)$. For radical ideals
$I,J$ one has $V(I)\subseteq V(J)$ if and only if $J\subseteq I$, since
$\sqrt I$ is the intersection of the primes containing $I$. Thus
$Z\mapsto I(Z)$, the intersection of the primes in $Z$, is an
inclusion-reversing bijection from closed subsets to radical ideals. A
descending chain $Z_1\supseteq Z_2\supseteq\cdots$ of closed sets gives
an ascending chain $I(Z_1)\subseteq I(Z_2)\subseteq\cdots$, which
stabilizes because $A$ is Noetherian; hence so does the chain of closed
sets.

*Finitely many components.* Call a closed subset *good* if it is a
finite union of irreducible closed subsets (the empty set being the
empty union). Suppose some closed subset is not good. By the descending
chain condition the set of such closed subsets has a minimal element
$Z$. Then $Z$ is nonempty and not irreducible, so $Z=Z_1\cup Z_2$ with
$Z_1,Z_2\subsetneq Z$ closed. By minimality $Z_1$ and $Z_2$ are good,
hence so is $Z$, a contradiction. Write
$X=C_1\cup\cdots\cup C_m$ with irreducible closed $C_j$ and discard
every $C_j$ contained in another. If $C$ is any irreducible closed
subset, then $C=\bigcup_j(C\cap C_j)$ forces $C\subseteq C_j$ for some
$j$, because an irreducible space is not a finite union of proper
closed subsets. Hence the maximal irreducible closed subsets, that is
the irreducible components, are exactly the remaining $C_j$, and there
are finitely many of them.
