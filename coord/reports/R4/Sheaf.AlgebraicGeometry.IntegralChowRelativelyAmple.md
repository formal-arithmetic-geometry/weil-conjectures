## What changed

Proved `AlgebraicGeometry.exists_integral_chow_relatively_ample` with its exact original
signature. Removed the four duplicate private helpers identified in the return:
`integralChow_tensorPullback_invertible`, `integralChow_tensorPullback_pair_iso`,
`integralChow_projective_ample_affine`, and `integralChow_projective_ample_affine_open`.
Added `import all Sheaf.AlgebraicGeometry.ChowRelativeAmpleTwistProperties` and directly
use its existing private `tensorPullback_invertible`, `tensorPullback_pair_iso`, and
`projective_ample_affine_open`. The affine helper is reached inside that existing proof.
Lean's proof-only `import all` makes these private declarations accessible without changing
their visibility or delivering any change to their module.

The modification is constructed as the schematic closure of the integral nonempty open of the
existing Chow modification. Its integral structure, properness, surjectivity, and isomorphism
over U are proved. Existing finite-coordinate reindexing supplies the required natural-number
dimension. The graph immersion over X is proper and hence closed; affine base change and the
existing projective ampleness theorem give the final quantified clause.

Updated the existing node’s proof, proof dependencies and proof origin to match. Only obsolete
entries were removed from its top-level tool approvals. No statement, definition, public
import, signature, visibility, target, or other module was changed. Added the gate-requested
change record `coord/changes/integral-chow-local-graded-instance.md` for the local annotation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.exists_integral_chow_relatively_ample`
(node `lem-weil-pbc-integral-chow-relatively-ample`). Added 0 holes; 0 holes remain.
No helper declarations are added. This is a proof, not a decomposition.

Single-file compilation through lcompile.py passed. The axiom check of the theorem reports
exactly `[propext, Classical.choice, Quot.sound]`. The final pruned version was compiled again.
Every new Lean line is at most 100 characters. Edge cases checked: N = 0 has one homogeneous
coordinate, arbitrary nonempty integral X is allowed without properness over k, and the empty
affine base open is handled by the affine-base result without a nonemptiness assumption.

## No longer needed

Removed direct proof imports:
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- `Sheaf.AlgebraicGeometry.ProjectiveAmpleInvertible`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible` (its proved theorem is
  reached inside the existing imported affine-open helper).
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`.
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification`.
- `WeilConjectures.AlgebraicGeometry.Ample`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`.

The required ProjectiveSpace, image, tensor-pullback and ampleness APIs are retained through
used imports. In particular removing a redundant direct import of an API does not assert its
node is mathematically unnecessary. Added the proved `ProjectiveSpaceReindexImmersion` module and a proof-only `import all`
of `ChowRelativeAmpleTwistProperties`.

Removed proof dependencies:
- `lem-chow-tuple-immersion`.
- `lem-sc-integral-scheme-stalks-in-function-field`.
- `lem-weil-pbc-projective-space-twist-glued-identification`.
- `lemma-nagata-scheme-image-restrict-open`.

The glued-identification node and module are unnecessary because the current twist definition
already uses usual pullback of the Proj twist; adjoint uniqueness gives the comparison with
tensor pullback. Integral-stalk computations are replaced by injectivity of section maps of
the scheme-theoretically dominant factor and Mathlib’s reducedness theorem. No tuple-product
lemma is needed: the existing liftBaseChange immersion instance cancels along the projection.
The separate open-restriction kernel lemma is replaced by the proved schematic-closure
restriction instance. Removed obsolete top-level tool approvals for `lem-chow-tuple-immersion`,
`lemma-nagata-scheme-image-restrict-open` and
`lem-weil-pbc-projective-space-twist-glued-identification`.

## Where the brief, the DAG or earlier work was wrong

The original proof’s glued-twist comparison reflects an older interface. In the current
source, `ProjectiveSpace.twist` is directly the usual pullback of `Proj.twist`; the standard
chart theorem is only needed to see that the finite coordinate type of the Chow modification
is nonempty. The dense open need not be shrunk to an affine one, since the locally Noetherian
Chow model makes its open inclusion quasi-compact. These shorten the original argument
without changing the statement or bypassing the unit route.

The finite-coordinate reindexing theorem and schematic-closure restriction theorem are
already proved source-library tools. They are used as tools, not replacements of any unit
statement or step. No new nodes are needed. The returned delivery was wrong to copy four private helper
statements from `ChowRelativeAmpleTwistProperties`; the lack of an applicable public
aggregate theorem did not prevent using its existing private helpers. All four copies are
now removed, and the exact existing lemmas are used directly via `import all`, as already
done for private lemmas elsewhere in this library. The modified file compiled cleanly in
3.2 seconds after this repair. The static gate requested a change record for the file-local
graded-ring instance annotation: `coord/changes/integral-chow-local-graded-instance.md`.
The annotation adds no global instance and changes no public signature. The downstream
check reports only `Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite`; no consumer
adaptation is forced. The original declaration
docstring is retained as the source proof plan; the node records the actual shorter Lean route.

Searches actually run through msearch.py: leanfinder for an integral proper surjective Chow
modification (returned basic integral/open and Proj facts, no full theorem); loogle for
`IsIntegral` (mostly commutative-algebra results, no full theorem); grep for
`Chow|chow|isReduced.*image` (irrelevant Salchow author matches). Direct source rg searches
found the existing schematic-closure, reindexing and projective ampleness arguments used here.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
