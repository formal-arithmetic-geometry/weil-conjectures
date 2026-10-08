+++
id = "lemma-weil-pbc-geometric-stalk-conservative"
kind = "lemma"
title = "Conservativity of geometric stalks"
order = 991
lean = ["AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map"]
uses = ["def-kun-separably-closed", "def-weil-pbc-etale-sheaves", "def-weil-pbc-geometric-stalks", "lemma-openclosed-point-ulift", "prop-weil-pbc-geometric-stalks-exact"]
+++
A morphism of etale abelian sheaves is an isomorphism if and only if it is an
isomorphism at every geometric stalk.

## Proof

The kernel and cokernel have zero geometric stalks. If a sheaf has zero
stalks, every local section vanishes on an etale neighbourhood of each point;
quasi-compact refinement on an etale object makes it locally zero on a cover,
hence zero by the sheaf axiom. Thus kernel and cokernel vanish.

## Detailed form

A morphism of etale sheaves of abelian groups is an isomorphism if and only
if it is an isomorphism at every geometric stalk
[def-weil-pbc-geometric-stalks].

## Proof

The kernel and cokernel have zero geometric stalks by exactness of the stalk
functors of [prop-weil-pbc-geometric-stalks-exact]. If a sheaf has zero
stalks, every local section vanishes on an etale neighbourhood of each point,
and quasi-compact refinement on an etale object makes it zero on a cover,
hence zero by the sheaf axiom of [def-weil-pbc-etale-sheaves]; so kernel and
cokernel vanish.
