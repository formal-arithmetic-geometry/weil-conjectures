+++
id = "lem-weil-pbc-proper-composition"
kind = "lemma"
title = "Properness is stable under composition"
order = 905
uses = ["def-weil-pbc-scheme-conventions"]
+++
The composite of proper [def-weil-pbc-scheme-conventions] morphisms is
proper.

## Proof

Separatedness, finite type and universal closedness are each stable under
composition in the sense of [def-weil-pbc-scheme-conventions]: the diagonal
of a composite is the composite of diagonals (hence a closed immersion), the
finite-type property passes through composites (finiteness of the generation
is transitive), and the composite of universally closed morphisms is
universally closed, since the base changes of the composite are composites of
base changes and composites of closed maps are closed. Hence the composite of
proper morphisms is proper.
