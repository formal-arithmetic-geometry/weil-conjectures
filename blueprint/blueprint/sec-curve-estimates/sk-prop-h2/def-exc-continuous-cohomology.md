+++
id = "def-exc-continuous-cohomology"
kind = "definition"
title = "Discrete modules and continuous group cohomology"
order = 961
uses = ["def-weil-abstract-derived-category"]
+++
For a profinite group $G$ and a finite ring $A$, a discrete
$A$-module with continuous $G$-action is an $A$-module $M$
with a $G$-action by $A$-linear automorphisms such that every
element has an open stabilizer. This is an abelian category.
Its invariant functor sends $M$ to
$M^G=\{m:gm=m\text{ for all }g\in G\}$.
The continuous cohomology $H^q(G,M)$ is its right derived functor,
formed in the ordinary
derived category.
Equivalently it is computed by the complex of continuous inhomogeneous
cochains $G^q\to M$, with the usual group-cochain differential.
