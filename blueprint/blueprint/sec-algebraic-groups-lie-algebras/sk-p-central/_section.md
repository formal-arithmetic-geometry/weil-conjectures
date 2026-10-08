+++
id = "sk-p-central"
kind = "section"
title = "A positive central representative"
order = 2526
uses = ["sk-d-central", "sk-d-monodromy", "sk-i-restriction", "sk-p-geometry", "sk-p-product"]
lean = ["AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_isPositiveCentralPair"]
+++
*Proposition (sketch).*

Every semisimple represented degree datum
admits a positive central pair $(N,z)$.

## Proof

The finite component group from [sk-p-geometry] supplies $m>0$ with
$F^m\in G^\circ$. By [sk-p-product], factor $F^m=ch$ with
$c\in Z(G^\circ)^\circ$ and $h\in H^\circ$, and choose a finite list
$g_1,\ldots,g_r$ meeting every coset of $G^\circ$ exactly once. Put

$$
N=mr,\qquad z=\prod_{i=1}^r g_i c g_i^{-1}.
$$

Since $G^\circ$ is normal, all
conjugates of $c$ lie in its abelian center. Replacing a coset
representative by $g_i u$, $u\in G^\circ$, leaves its factor unchanged;
the factors commute. Left multiplication permutes the component cosets,
so conjugation by any $g\in G$ fixes their product $z$.
By [sk-i-restriction], every commutator in $G$ lies in $H$.
Thus each $g_i c g_i^{-1}$ has the same $H$-coset as $c$, namely
$HF^m$, and multiplication yields $z\in HF^{mr}$.
There is at least the identity coset, so $r>0$ and $N=mr>0$.

Uses: [sk-d-central], [sk-d-monodromy], [sk-i-restriction], [sk-p-geometry], [sk-p-product]
