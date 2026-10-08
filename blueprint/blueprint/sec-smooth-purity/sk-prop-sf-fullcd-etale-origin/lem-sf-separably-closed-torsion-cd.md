+++
id = "lem-sf-separably-closed-torsion-cd"
kind = "lemma"
title = "Torsion cohomological dimension of a separably closed field"
order = 1789
uses = ["def-sc-etale-torsion-cd", "def-weil-pbc-etale-sheaves", "def-weil-pbc-etale-site", "lem-exc-field-discrete-modules"]
+++
Let $K$ be a separably closed field. Then
$\operatorname{cd}_{\rm tor}(K)\leq0$ in the sense of
[def-sc-etale-torsion-cd]: for every
torsion étale sheaf $F$ on
$\operatorname{Spec}K$ and every $q>0$ one has
$H^q(\operatorname{Spec}K,F)=0$.

## Proof

Let $F$ be a sheaf of abelian groups on the
small étale site of
$\operatorname{Spec}K$. Since $K$ is separably closed, every étale
$K$-scheme is a disjoint union, finite or infinite, of copies of
$\operatorname{Spec}K$; these objects form a basis of the site which is
closed under fibre products, and for an object
$\bigsqcup_{i\in I}\operatorname{Spec}K$ the inclusions of the
components are an étale covering whose pairwise fibre products are empty,
so the sheaf axiom presents
$F(\bigsqcup_{i\in I}\operatorname{Spec}K)$ as
$\prod_{i\in I}F(\operatorname{Spec}K)$. Hence $F$ is constant and is
determined by the abelian group $F(\operatorname{Spec}K)$, and the global
section functor is an equivalence onto abelian groups; it is therefore
exact and its higher derived functors vanish. This proves the assertion
for every torsion sheaf, and the dictionary of
[lem-exc-field-discrete-modules] records the same conclusion for the
étale module sheaves of a finite coefficient ring, which is the case used
below.
