+++
id = "lem-kun-bc-base-change"
kind = "lemma"
title = "Base change maps are compatible with further base change"
order = 1751
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-derived-exchange", "def-weil-pbc-inverse-image"]
+++
Given a
cartesian square as in
[def-weil-pbc-cartesian-square] and a morphism $u:Y''\to Y'$,
form the square obtained by pulling all four corners and maps back
along $u$. Under the canonical pseudofunctorial identifications,
the pullback along $u$ of the original exchange morphism of
[def-weil-pbc-derived-exchange] is the exchange morphism of the
pulled-back square.

## Proof

Both morphisms are mates (under the derived adjunctions of
[def-weil-pbc-inverse-image]) of composites of the canonical
$\theta$-isomorphism of
[def-weil-pbc-cartesian-square] with the counit
$\varepsilon_f$, and the $\theta$'s are compatible with the
identifications for the pulled-back square (compatibility with
pasted squares of [def-weil-pbc-cartesian-square]); hence the
identity.
