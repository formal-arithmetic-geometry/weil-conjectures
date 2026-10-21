## What changed

Proved the unchanged `AlgebraicGeometry.SmoothSectionCentredCoordinates.exists_centred_coordinates`
from two new, separately proved results. `SmoothSectionAffineCoordinates` builds the geometric
chart and its regular equations from the already proved adopted-source
`Scheme.Hom.exists_etale_coordinates_of_mem_range`. `RegularIdealConormalCoordinates` constructs
the conormal basis with its actual representatives, proves the monomial formula and the affine
bijectivity of the canonical symmetric comparison, and provides a free frame. The item assembles
these charts, proves regular immersion and finite local freeness, and applies the quasi-coherent
affine-cover isomorphism criterion to the canonical comparison's underlying module morphism.

The original `Chart` and theorem signatures are unchanged. No source-library declaration,
definition, attribute or public import was edited. Updated the item's DAG proof route and
attached the existing ring-coordinate theorem as a finished source-library dependency.

Validation: all three modules compiled on the project server through `lcompile.py`.
The conormal theorem compiled in the dependency build; the affine chart compiled in 6.7 seconds
and the final item in 5.8 seconds. No warnings or proof holes remain in these files.
Delivery preflight supplies the independent interface, dependency and axiom checks.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SmoothSectionCentredCoordinates.exists_centred_coordinates`.
Added zero holes. The two new theorem proofs are complete in the packet:
`AlgebraicGeometry.SmoothSectionCentredCoordinates.exists_affineChart` and
`AlgebraicGeometry.ConormalGradedAlgebra.regular_ideal_conormal_coordinates`.
No `sorry` remains in any delivered Lean file; no statement is left for a later worker.
The existing dependency theorems are used with their published signatures.

## No longer needed

Removed these proof-only imports from the item:

- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.CategoryTheory.Limits.MorphismProperty`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.RingHom.StandardSmooth`
- `Mathlib.RingTheory.Smooth.Flat`
- `Sheaf.RingTheory.RegularSequenceGradedPolynomial`
- `WeilConjectures.AlgebraicGeometry.AffineConormalFrame`

The following original planned dependencies are replaced by the already proved upstream
ring-coordinate theorem or direct affine/flat/regular-sequence APIs; the Lean proof does not
import their statement modules:

- `lem-sc-standard-smooth-local-relative-dimension`
- `lem-sc-standard-smooth-etale-polynomial-chart`
- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-etale-base-change-finite-limits`
- `lem-weil-pbc-etale-composition-cancellation`
- `lem-weil-pbc-affine-source-morphism-separated`
- `lem-weil-pbc-separated-base-change`
- `lem-weil-pbc-etale-section-clopen-immersion`
- `def-pc-fibre-product`
- `lem-weil-pbc-etale-ring-map-iff-etale-affine`
- `lem-weil-pbc-etale-algebra-flat`
- `lem-trf-flat-tensor-preserves-injection`

The graded-polynomial, conormal presentation, affine conormal frame, free symmetric-polynomial
comparison, quasi-coherent symmetric comparison and affine-cover isomorphism nodes remain
needed, directly or through the new conormal lemma. Their removal from the item's direct
`proof_deps` or `tool_uses` is only a relocation to the corresponding new dependency node.
No Lean module is withdrawn, and no unused upstream declaration is removed. Other users of
these planned dependencies are unaffected.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The existing source library already contains the hard
centred ring-coordinate construction, so redoing the geometric chart refinements was unnecessary.
The available source conormal-basis theorem uses reverse regularity; the item's regular list
uses the forward Mathlib convention. The new private independence proof therefore uses the
published regular-sequence homogeneous-relation theorem in degree one, without adding a reverse
regularity assumption or changing any interface.

The edge cases are handled by the proofs: point indexing gives an empty cover for the empty
base; the polynomial weak-regularity and nonzero quotient argument include d = 0; the monomial
induction includes exponent zero. Affineness is used only for the chosen opens and their closed
section inverse images, not for intersections of arbitrary affine opens.

## New nodes

`lem-sc-smooth-section-ring-coordinates` attaches the existing proved source declaration
`AlgebraicGeometry.Scheme.Hom.exists_etale_coordinates_of_mem_range`; it introduces no module,
no declaration and no hole.

`lem-sc-smooth-section-affine-coordinates` records the new `AffineChart` witness and
`exists_affineChart`, the geometric and regular-equation part of the original chart.

`lem-sc-regular-ideal-conormal-coordinates` records
`regular_ideal_conormal_coordinates`, the independent regular-ideal conormal calculation.
No existing definition or statement changed, so there is no change record.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
