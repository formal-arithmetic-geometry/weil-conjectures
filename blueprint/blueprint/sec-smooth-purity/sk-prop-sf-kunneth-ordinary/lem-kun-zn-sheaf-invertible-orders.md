+++
id = "lem-kun-zn-sheaf-invertible-orders"
kind = "lemma"
title = "Modules over $\\kunZn$ have invertible orders"
order = 1681
uses = ["def-kun-torsion-invertible", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site"]
+++
Let $K$ be a field and $n\in I_K$ an integer invertible in $K$
([def-kun-torsion-invertible]). For every scheme $T$ over $K$,
every sheaf of $\kunZn$-modules on the small etale site of $T$,
[def-weil-pbc-etale-site], has orders invertible in $K$.

## Proof

Let $F$ be a sheaf of $\kunZn$-modules on $T_{\Et}$. The ring
$\kunZn$ is annihilated by $n$, so multiplication by $n$ is the
zero endomorphism of $F$: every section of $F$, hence every
element of every geometric stalk, is killed by $n$. As $n\in I_K$,
the condition defining orders invertible in $K$ of
[def-kun-torsion-invertible] is satisfied.
