## What changed

Proved `AlgebraicGeometry.finite_graded_proj_projective` without changing its statement
or any existing definition. Added two fully proved reusable modules:
`Sheaf.AlgebraicGeometry.VeroneseGeneration` and
`Sheaf.AlgebraicGeometry.VeroneseProjIso`. The first implements the weighted-monomial
argument, including the case with no positive generators by padding with zero.
The second constructs the fraction maps, proves they are ring equivalences, checks
the overlap maps and glues inverse scheme maps. Projectivity uses existing common-degree
ample twists and the affine-base immersion theorem, upgraded to a closed immersion
using Mathlib properness. Updated the original DAG route to match.

All three modules compile cleanly through lcompile.py --all. No source-library file,
public import of the assigned module, existing signature, or target was changed.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.finite_graded_proj_projective`
(`lem-sfb-finite-graded-proj-projective`). Holes closed: 1 of 1. Holes added: 0.
No sorry remains in any delivered Lean file. Both new public theorems are fully proved:
`GradedAlgebra.exists_veronese_generators` and
`AlgebraicGeometry.exists_veronese_proj_iso`.

The proof uses existing declarations, including the Veronese grading and the common-degree
ample-twist theorem. Their upstream holes are unchanged; this is a proof from existing
stated dependencies, not a claim that the entire target axiom closure is already closed.

## No longer needed

Removed proof imports from the assigned module:
- `Mathlib.AlgebraicGeometry.Gluing` (used privately in the new chart-isomorphism module).
- `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`.
- `Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle`.
- `WeilConjectures.AlgebraicGeometry.Ample` (provided by the new proof dependencies).
- `Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective`.
- `Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition`.
- `Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`.

The direct chart proof uses Mathlib `awayMap`, `pullbackAwayιIso`, and cover gluing,
so the old chart-ring-cocycle and basic-open-intersection proof nodes are unnecessary
for this route. The ample-twist/properness proof replaces the polynomial quotient,
scalar extension, finite projective bundle and projective-composition route. The
following original node dependencies are no longer called directly by the assigned
proof (definitions remain available through the statements, and other consumers may
still need these modules):
- `def-pc-proj`.
- `def-weil-closed-immersion`.
- `def-weil-finite-type-morphism`.
- `def-nagata-homogeneous-localization-degree-zero`.
- `def-weil-affine-spectrum`.
- `prop-nagata-proj-standard-open`.
- `lem-weil-pbc-proj-basic-open-intersection`.
- `lemma-nagata-proj-chart-ring-cocycle`.
- `lem-weil-pbc-scheme-morphism-gluing`.
- `prop-nagata-relative-proj-functoriality`.
- `def-kun-projective`.
- `def-weil-finite-integral-morphism`.
- `lem-trf-finite-projective-bundle`.
- `def-weil-pbc-ample-invertible-module`.
- `lem-trf-projective-bundle-to-h-projective`.
- `lem-trf-h-projective-composition`.
- `lem-nagata-affine-proj-scalar-extension`.
- `def-nagata-projective-space-base-change`.

The six old `tool_uses` approvals are removed, since none of those tools is used by the
new proof. No existing declaration or module is withdrawn. The unit's realized route
is unchanged (this supporting node's unit record has no realized step to bypass).

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The DAG prescribed more projective-bundle
machinery than necessary: Mathlib already proves Proj proper, and the existing ample
immersion theorem plus the existing common-degree twist theorem gives H-projectivity.
The canonical Veronese chart comparison can use all homogeneous S charts directly;
only the covering argument needs d-th powers of original homogeneous elements.
The zero ring, grading concentrated in degree zero, and nilpotent chart denominators
require no nontriviality or domain hypotheses in either new lemma.

## New nodes

`lem-sfb-veronese-generation`: the original proof's monomial steps, generalized to
commutative coefficient rings and finite generation over degree zero. Fully proved
in `Sheaf.AlgebraicGeometry.VeroneseGeneration`.

`lem-sfb-veronese-proj-iso`: the original proof's chart and gluing steps, valid for
every positive d with no finite-type hypotheses. Fully proved in
`Sheaf.AlgebraicGeometry.VeroneseProjIso`.

No change record is needed: no existing definition or statement changed.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
