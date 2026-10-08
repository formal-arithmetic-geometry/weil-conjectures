+++
id = "lem-weil-pbc-exchange-identity-pasting"
kind = "lemma"
title = "Identity and pasting equations for exchange"
order = 1044
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "lemma-weil-pbc-derived-exchange-replacement"]
+++
The transformation $\Ex_{\square}$ of the derived exchange morphism
[def-weil-pbc-derived-exchange] is the identity for an identity
square. For horizontally or vertically pasted cartesian squares
[def-weil-pbc-cartesian-square], the exchange morphism of the outer
rectangle equals the composite of the exchange morphisms of the two inner
squares after inserting the canonical associativity isomorphisms for inverse
and derived direct images.

## Proof

Both equations are the mate versions of the identity and pasting laws for
$\theta_\square$ recorded in [def-weil-pbc-cartesian-square],
transported through the adjunction calculus for the adjunctions
$f'^{-1}\dashv Rf'_*$ and $f^{-1}\dashv Rf_*$ of the squares involved. By
[lemma-weil-pbc-derived-exchange-replacement] every displayed map is the
specified derived exchange morphism of
[def-weil-pbc-derived-exchange].
