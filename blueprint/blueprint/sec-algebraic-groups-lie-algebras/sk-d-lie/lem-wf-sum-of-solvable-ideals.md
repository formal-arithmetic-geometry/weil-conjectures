+++
id = "lem-wf-sum-of-solvable-ideals"
kind = "lemma"
title = "Sum of two solvable ideals"
order = 2466
uses = ["def-wf-lie-algebra"]
+++
In a finite-dimensional Lie algebra $\mathfrak g$, the sum of two
solvable ideals (in the sense of [def-wf-lie-algebra]) is solvable.

## Proof

Let $I,J\subseteq\mathfrak g$ be solvable ideals, with derived lengths
$a$ and $b$, and put $K=I+J$, an ideal of $\mathfrak g$. The
second isomorphism theorem gives
$K/I\simeq J/(I\cap J)$, a quotient of the solvable Lie algebra $J$,
hence solvable of derived length at most $b$; therefore
$K^{(b)}\subseteq I$. Subalgebras of solvable Lie algebras are solvable,
so $(K^{(b)})^{(a)}\subseteq I^{(a)}=0$, that is,
$K^{(a+b)}=0$. Hence $K$ is solvable.
