+++
id = "prop-weil-pbc-projective-line"
kind = "theorem"
title = "Projective-line proper base change"
order = 1183
tags = ["latex:proposition"]
uses = ["def-weil-pbc-injective-acyclicity-property", "def-weil-pbc-property", "lemma-weil-pbc-geometric-stalk-conservative", "lemma-weil-pbc-p1-exchange-geometric-stalk", "lemma-weil-pbc-property-iff-acyclicity", "prop-weil-pbc-proper-curve-sepclosed-invariance"]
+++
For every scheme $S$, the projection $\mathbf P^1_S\to S$ satisfies
$\mathsf{PBC}$.

## Proof

At every geometric $\bar t\to T$, the exchange map is the field-extension
map of the preceding lemma. The two residue fields are separably closed and
the fibre is a proper curve, so proper-curve invariance makes this map an
isomorphism. Geometric stalk conservativity gives an isomorphism of every
$R^q$ sheaf. Specializing to inverse images of injective
$\mathbf F_\ell$-module sheaves gives $\mathsf{IA}$ after every base change;
the S0 equivalence gives $\mathsf{PBC}$.

## Detailed form

For every scheme $S$, the projection $\mathbf P^1_S\to S$ satisfies
$\mathrm{PBC}$ in the sense of [def-weil-pbc-property].

## Proof

Let $I$ be injective in $\mathbf F_r$-module sheaves on $\mathbf P^1_S$ and
make an arbitrary base change. On every geometric stalk,
[lemma-weil-pbc-p1-exchange-geometric-stalk] identifies the exchange map with
pullback between proper curves over separably closed fields;
[prop-weil-pbc-proper-curve-sepclosed-invariance] makes it an isomorphism. Since
$R^qp_*I=0$ for $q>0$, the target stalks $R^qp'_*g'^{-1}I$ vanish for $q>0$,
and conservativity of geometric stalks gives $\mathrm{IA}_r$ for the
projection; the equivalence between $\mathrm{PBC}$ and $\mathrm{IA}$ gives
$\mathrm{PBC}$.
