## What changed

Completed `AlgebraicGeometry.closed_dominant_dimension` in
`Sheaf.AlgebraicGeometry.ClosedDominantDimension`, with its signature and public imports
unchanged. The upper bound uses `local_dimension_formula` and Mathlib's stalk/coheight
identity. For the reverse bound, the generic pullback is proved integral, its function
field is identified over the actual base function field, and
`exists_generic_fibre_closed_chain` supplies a strict chain. The closure of its endpoint
maps by a closed specializing surjection onto the base. Height/coheight concatenation gives
the lower bound, including infinite dimensions. The proper finite-extension clause follows
from closedness and transcendence degree zero.

Added proof imports for `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`WeilConjectures.Mathlib.Topology.KrullDimension`, and
`Mathlib.RingTheory.AlgebraicIndependent.Transcendental`. All new helper theorems are private
and proved. Updated the existing node's proof text to describe the formal argument.
No statement or definition changed, and no consumer adaptation is necessary.

Validation: `lcompile.py` compiled the complete module with exit code 0, no warnings,
in 17.1 seconds. Source checks confirm that the theorem signature and public imports are
verbatim unchanged, there are zero `sorry` tokens, all Lean lines meet the 100-column limit,
and the node's proof-dependency list still equals the union of its proof steps' uses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.closed_dominant_dimension`
(`lem-trf-closed-dominant-dimension`). Proved 1 of 1 original sorries; added 0; split off 0.
There are no remaining sorries in the delivered module. The proof intentionally uses the
existing stated dependencies `AlgebraicGeometry.local_dimension_formula` and
`AlgebraicGeometry.exists_generic_fibre_closed_chain`, whose own proofs remain separate items.

## No longer needed

None. Every original proof-dependency module and node remains needed. No public import,
module, declaration, or unit-route step was removed. The generic-chain theorem's closedness,
finite-residue, and first-endpoint conclusions are stronger than the chain argument needs;
its strict chain and transcendence-degree conclusions suffice here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The affine localization description in the original plan can
be implemented more directly using flat preimmersions and their stalk isomorphisms. The
explicit concatenation of lifted base chains is packaged by the existing specializing-map
dimension comparison and Mathlib's height-plus-coheight formula. The proof route and its
five declared dependencies are retained. The algebra compatibility is proved explicitly,
so the transcendence degree uses exactly the function-field map in the theorem statement.
The zero-length and infinite-dimension cases are covered by the same inequalities.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
