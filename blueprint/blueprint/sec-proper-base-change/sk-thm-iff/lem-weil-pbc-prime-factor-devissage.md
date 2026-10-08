+++
id = "lem-weil-pbc-prime-factor-devissage"
kind = "lemma"
title = "Prime-factor devissage"
order = 1086
uses = ["def-weil-pbc-etale-sheaves"]
+++
Let $n>1$, choose a prime $r\mid n$, and let $F$ be killed by $n$. There is a
natural exact sequence

$$
 0\longrightarrow F[r]\longrightarrow F
 \xrightarrow{r} rF\longrightarrow0,
$$

where $F[r]$ is killed by $r$ and $rF$ is killed by $n/r$. Thus a property of
torsion sheaves [def-weil-pbc-etale-sheaves] stable under short exact
sequences and known for prime-torsion sheaves holds for every sheaf killed by
a positive integer.

## Proof

The displayed sequence is the kernel--image sequence for multiplication by
$r$ in the abelian category of etale sheaves, whose kernels and images are
computed sectionwise as in [def-weil-pbc-etale-sheaves]. The claims about the
orders follow from $r\cdot F[r]=0$ and $n/r\cdot rF=0$. The induction on the
number $\sum_\ell v_\ell(n)$ of prime factors of $n$, using this sequence at
each step, proves the stability assertion.
