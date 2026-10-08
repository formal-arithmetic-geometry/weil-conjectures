+++
id = "lemma-constructible-torsor-trivialises"
kind = "lemma"
title = "Torsors under finite locally constant sheaves"
order = 1297
uses = ["def-constructible-finite-locally-constant"]
+++
Let $\mathcal G$ be a finite locally constant sheaf of groups on $\et X$
and let $P$ be a $\mathcal G$-torsor. Then $P$ is trivial on an étale
cover of $X$.

## Proof

Working on the members of a trivialising cover of $\mathcal G$ we may
assume $\mathcal G=G_X$ for a finite group $G$. A $G_X$-torsor is
representable by a scheme $P\to X$ finite étale (locally on $X$ it is
$\bigsqcup_{g\in G}X$, and the transition functions are locally constant
permutations; see SGA 4); since $P\to X$ is étale and
surjective it is an étale cover, and $P$ restricted to $P$ has the
tautological section, so it is trivial there.
