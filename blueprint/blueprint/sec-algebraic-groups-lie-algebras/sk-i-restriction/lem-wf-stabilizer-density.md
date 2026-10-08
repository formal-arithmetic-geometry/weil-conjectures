+++
id = "lem-wf-stabilizer-density"
kind = "lemma"
title = "Closed stabilizers and density"
order = 2515
uses = ["def-wf-geometric-monodromy-group"]
+++
Let $S\subseteq V$ be a vector subspace. The stabilizer
$\operatorname{Stab}_{\operatorname{GL}(V)}(S)$ is Zariski closed.
Consequently $S$ is $\Pi$-stable if and only if it is
$H_{\mathrm{geom}}$-stable.

## Proof

Choose a basis whose first vectors span $S$. The condition that a
matrix preserve $S$ says that each lower-left matrix entry is zero,
which is a finite list of polynomial equations. The stabilizer is
therefore closed. If $S$ is $\Pi$-stable, this closed stabilizer
contains $\rho(\Pi)$, hence contains its Zariski closure by
[def-wf-geometric-monodromy-group]; the converse is immediate.
