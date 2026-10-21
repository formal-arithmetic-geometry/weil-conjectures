## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleLocalizedRingMateGraphEvaluation` with its
statement and all definitions unchanged. Private proved helpers compute the actual
Kan/sheafification adjunction unit, identify the specified constant coefficient map
under restriction, and evaluate the constant-sheaf adjunction on sections. Naturality
then proves the mate and graph formulas, the diagonal isomorphism, the integer-unit
identity, and the pulled global-section formula.

The node proof now records these calculations. No new public declarations or modules,
statement changes, definition changes, or consumer adaptations are needed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.proEtaleLocalizedRingMateGraphEvaluation`
(`lem-sfb-localized-ring-mate-graph-evaluation`).
No holes added or split off. No `sorry` remains in the delivered Lean module.
The full module compiled cleanly through `lcompile.py` in 21.9 seconds (exit 0).

## No longer needed

Removed the private import `Sheaf.CategoryTheory.SiteInverseImageTensor`.
The proof does not need `lem-weil-pbc-left-exact-site-inverse-image-tensor`, removed
from this node's proof dependencies, final proof step, and obsolete tool-use approval.
The integer-unit map is already explicitly defined through normalized restriction;
its compatibility with the specified constant inverse-image map follows directly
from adjunction injectivity and sheafification uniqueness on constant sections.
No module is withdrawn, and this does not claim the tensor module is unused elsewhere.
All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned constant-unit argument can be made directly
with the defined maps; invoking a general tensor-coherence theorem is unnecessary.
The existing comparison's `coprojection` and `sheafIso_inv` fields suffice for the
projection-unit computation for arbitrary ring and additive sheaves.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
