+++
id = "lemma-weil-pbc-completed-exchange-coherence"
kind = "lemma"
title = "Completed exchange coherence"
order = 1348
uses = ["def-weil-pbc-completed-base-change-map", "lem-weil-pbc-exchange-identity-pasting", "lemma-weil-pbc-completed-map-reduction", "lemma-weil-pbc-r-lim-levelwise-isomorphism"]
+++
The completed exchange map is natural in $K$, is the identity for identity
squares, and commutes with horizontal and vertical pasting.

## Proof

At every finite level these equations are the S0/S8 equations. They commute
with the tower transitions by naturality of coefficient reduction. Apply
$R\varprojlim$ to each equality and conjugate by the same reconstruction,
projection-formula, and direct-image/limit isomorphisms used in the definition.
The resulting equations are precisely the completed equations.

## Detailed form

Completed exchange of [def-weil-pbc-completed-base-change-map] is
natural in $K$, equals the identity for identity squares, and satisfies
horizontal and vertical pasting after the canonical associativity
isomorphisms.

*Source note:* no Stacks Project entry states these coherence properties of
the completed exchange: Theorem 61.30.1 ([Tag
09C9](https://stacks.math.columbia.edu/tag/09C9)) asserts only that the
base-change map is an isomorphism, Lemma 61.20.2 ([Tag
099N](https://stacks.math.columbia.edu/tag/099N)) gives the functoriality of
$Lf^*_{comp}$ and of $Rf_*$ alone, and the nearest recorded coherence of the
two ingredients is the commutativity of the projection formula with the base
change map, Remark 21.50.2 ([Tag
0E48](https://stacks.math.columbia.edu/tag/0E48)), stated for a single
square of ringed topoi without coefficients or completion. The blueprint
adds naturality in $K$, the identity-square statement and horizontal and
vertical pasting for the completed exchange.

## Proof

The finite-level reductions of [lemma-weil-pbc-completed-map-reduction]
satisfy the identity and pasting laws of the exchange identity-and-pasting
lemma levelwise, and the tower morphisms preserve these compatible
equalities, so the completed map of
[def-weil-pbc-completed-base-change-map] inherits them.
