+++
id = "sk-p-readout"
kind = "section"
title = "Central scalars and weight readout"
order = 2552
uses = ["sk-d-central", "sk-d-linear", "sk-d-monodromy", "sk-d-tangent", "sk-d-weights", "sk-i-restriction", "sk-r-linear-library"]
lean = ["AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.detWeight_eq_of_isPositiveCentralPair"]
+++
*Proposition (sketch).*

Fix a real weight character $\lambda$,
monodromy data and a
positive central pair $(N,z)$.
Let $Q\ne0$ be a $W$-subquotient of a
rational $G$-representation, with
finite geometric determinant. If $z$ acts on
$Q$ as a scalar $c_Q$, then

$$
\dw_\lambda(Q)=\frac{\lambda(c_Q)}{N}.
$$

The scalar-action hypothesis holds whenever $Q$ is simple.
The determinant weight is independent of the chosen degree-one lift.

## Proof

By [sk-i-restriction], $Q$ is rational for $G$, and a simple
$W$-subquotient is simple for $G$. If simple, the central element $z$
acts by a nonzero scalar by Schur's lemma in r:linear-library.
For the general
scalar-action case, let $r=\dim Q$ and let $\delta:G\to k^\times$
be its rational determinant character. Its restriction to $H$ has
finite image: the inverse image of the finite closed set
$\delta(\rho(P))$ is closed and contains the dense subgroup $\rho(P)$.
The character of [sk-d-weights] kills finite-order elements:
if $a^m=1$ with $m>0$, then $m\lambda(a)=\lambda(a^m)=0$.
Write $z=hF^N$ using [sk-d-central]. Taking determinants gives
$c_Q^r=\delta(h)\delta(F)^N$. Apply the character of [sk-d-weights],
which kills the finite-order factor $\delta(h)$, and divide by $rN$.
Replacing $\gamma$ by $u\gamma$, $u\in P$, also changes its determinant
by a finite-order factor, proving independence of the lift.
This argument assumes the pair; it does not use its existence theorem.

Uses: [sk-d-central], [sk-d-linear], [sk-d-monodromy], [sk-d-tangent], [sk-d-weights], [sk-i-restriction], [sk-r-linear-library]
