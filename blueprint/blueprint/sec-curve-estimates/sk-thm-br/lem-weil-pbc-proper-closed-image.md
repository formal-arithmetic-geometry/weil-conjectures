+++
id = "lem-weil-pbc-proper-closed-image"
kind = "lemma"
title = "A proper morphism has closed image"
order = 907
uses = ["def-weil-pbc-scheme-conventions"]
+++
The image of a proper [def-weil-pbc-scheme-conventions] morphism $f:X\to Y$
is closed in $Y$ (a proper morphism is universally closed, hence closed, and
its image is a closed subset carrying an induced $Y$-scheme structure).

## Proof

A proper morphism is universally closed, hence closed: by
[def-weil-pbc-scheme-conventions] every base change of a proper morphism is a
closed map, so $f$ itself is a closed map, and the identity base change gives
the asserted closedness. Its image is therefore a closed subset of $Y$,
carrying the induced closed subscheme structure of the scheme-theoretic
image, and $f$ restricted to its image is a proper surjection.
