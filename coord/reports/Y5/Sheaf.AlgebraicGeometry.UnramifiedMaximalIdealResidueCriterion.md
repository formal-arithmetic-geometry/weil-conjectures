## What changed

Proved `AlgebraicGeometry.unramified_neighbourhood_iff_maximalIdeal_residue` in
`Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion`, preserving its statement,
public imports, and the existing DAG route (Stacks Tag 02GF, (1) iff (6)).

The proof first identifies an unramified neighbourhood with formal unramifiedness of the
actual stalk map. In the forward direction, the open inclusion's stalk isomorphism transports
formal unramifiedness back to the original stalk. In the reverse direction, the existing
`FormallyUnramified.exists_neighbourhood_of_stalkMap` theorem gives the neighbourhood;
local finite type and the open diagonal follow from Mathlib instances.

On the resulting local-ring algebra, Mathlib's maximal-ideal criterion supplies both
directions. The proof explicitly identifies its induced residue-field algebra with the one
from `f.residueFieldMap x`, so finiteness and separability concern the map in the statement.
A declaration-local transparency option handles the scheme/open carrier identifications.

Single-file compilation passed with no warnings. A temporary `#print axioms` check reported
only `propext`, `Classical.choice`, and `Quot.sound`. No definitions or other modules changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.unramified_neighbourhood_iff_maximalIdeal_residue`
(node `lem-trf-unramified-maximal-ideal-residue-criterion`).

Holes added: 0. Holes remaining in the delivery: 0. Split-off statements: 0.

## No longer needed

None. Both existing proof imports are used: Mathlib's formally-unramified morphism and
local-ring API, and the source library's stalk-to-neighbourhood theorem. All four declared
proof dependencies remain used, with the three Mathlib leaves applied directly through
their declarations and instances. No modules or nodes are withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

None. The stated two-step argument is sufficient. The local-ring criterion is applied to
the algebra of the actual stalk homomorphism; the finite residue-field condition in the
reverse implication is redundant but retained exactly as stated. The unit route is preserved.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
