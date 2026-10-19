## What changed

Proved `AlgebraicGeometry.Etale.finiteTorConstructible_etale_localizing_eq_top`
in `Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration` by the four-step
argument already recorded in `det-ctf-finite-comparison-whole`.
The finite-ring theorem supplies the detecting family and ambient coproducts;
the stipulated étale compactness theorem supplies compactness. Vanishing maps
from the coproduct into shifts force all maps from shifted generators to vanish.
Detection then makes the zero map to the object an isomorphism. The compact-generator
telescope and induction on its stages put every object in each candidate subcategory.

Added the proof-only import `Mathlib.Algebra.CharP.CharAndCard` to establish
invertibility of the coefficient prime in the standing algebraic closure. Added
a proof-local zero-object instance. No signatures, definitions or public imports
changed. The existing DAG proof and proof dependencies describe this proof unchanged.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.finiteTorConstructible_etale_localizing_eq_top`
(node `det-ctf-finite-comparison-whole`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No intermediate statements were split off. `lcompile.py` compiled the complete
module without errors or warnings in 3.4 seconds.

## No longer needed

Removed the redundant proof import `Sheaf.CategoryTheory.WeakTriangulatedGenerator`;
its definitions are publicly imported by `Sheaf.CategoryTheory.CompactGeneratorsBuildObjects`.
The definition node `def-pc-generators` remains used. All five stated proof dependencies
remain used, and the unit's compactness, detection and telescope route is unchanged.
No DAG nodes or mathematical dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. Mathlib's `ext_of_isTriangulatedClosed₃` supplies the
third-object closure derived from rotation and middle-object closure, implementing
the two rotations in the stated argument.

The earlier attempt had no compiler verdict because the compilation service did not
respond. The resumed dry run produced actual Lean diagnostics: the draft needed a
proof-local `Zero` instance for the ambient category. Adding `HasZeroObject.zero'`
resolved both errors. Removed the stale sandbox change record describing an absent
adjunction import: the final delivery changes only the proof and its private imports,
so it requires no definition or statement change record.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
