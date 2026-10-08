+++
id = "p-central"
kind = "theorem"
title = "A positive central representative"
order = 2527
tags = ["latex:proposition"]
uses = ["d-central", "d-monodromy", "lem-ag-closure-commutators", "lem-wf-algebraic-component-cosets", "p-product"]
lean = ["AlgebraicGeometry.Monodromy.RepresentedDegreeDatum.exists_isPositiveCentralPair"]
+++
Every semisimple represented degree datum ([d-monodromy])
admits a positive central pair ([d-central]) $(N,z)$, that is $N>0$ and
$z\in Z(G)\cap HF^N$.

## Proof

The finite component group from [lem-wf-algebraic-component-cosets]
supplies $m>0$ with $F^m\in G^\circ$. By [p-product], factor $F^m=ch$ with
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
By [lem-ag-closure-commutators], every commutator in $G$ lies in $H$,
so $g_icg_i^{-1}=(g_icg_i^{-1}c^{-1})c\in Hc$; and
$c=F^mh^{-1}\in F^mH=HF^m$ because $H$ is normal.
Thus each $g_i c g_i^{-1}$ has the same $H$-coset as $c$, namely
$HF^m$, and multiplication yields $z\in HF^{mr}$.
There is at least the identity coset, so $r>0$ and $N=mr>0$.
