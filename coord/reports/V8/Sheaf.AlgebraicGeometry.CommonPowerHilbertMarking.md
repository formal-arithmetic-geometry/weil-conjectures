## What changed

Proved `AlgebraicGeometry.HilbertCoefficient.commonPowerHilbertMarking`, preserving its
complete signature and every public definition/import. Added seven proved private helpers
for coherence, affine stalk ideals, finite order thresholds, the regular local tangent cone,
its homogeneous power formula, detection of powers in maximal-ideal powers, and the
common-power coefficient order criterion. The Hilbert equality germ follows directly from
`coefficient_equality_germ` on the neighbourhood it supplies.

The tangent-cone proof uses existing declared tools
`lem-weil-pbc-regular-local-generators-regular-sequence` and
`lem-pur-regular-sequence-graded-polynomial`, together with
`lem-weil-pbc-associated-graded-ring-structure`. A minimal generating family of a regular
local maximal ideal is regular; its graded ring is polynomial over the residue field.
The first nonzero homogeneous class cannot acquire a zero positive power. This proves
both directions of the coefficient power test without a new hole or a marked-ideal
package. These are algebraic tools, not a replacement of the unit route. The unit's
`realized` lists do not name this item, and no unit or chapter record changes.

Updated only steps 1--3, their dependency union, and proof provenance in the item's node.
The other three theorem proofs and their planned DAG steps remain unchanged. There are
no changes to other existing Lean modules, no interface repairs, and no forced adaptations.

Validation: single-file server compile passed in 13.7 seconds before the final switch to
the node-attached finite-type ideal-module theorem. The delivery tool compiles the final
packet and runs preflight. Search used LeanFinder, Loogle, the logged grep service, and
local searches in both library roots and Mathlib. The semantic search returned power-series
order lemmas; Loogle returned ideal-span/power lemmas, with no match for the whole theorem.

Edge cases: the proof covers the empty coefficient family (zero ideal, vacuous order tests),
zero and unit coefficients, degree zero in the tangent cone, zero-dimensional regular
stalks (empty parameter list), and nonclosed scheme points. The power-detection helper
requires a positive exponent; positivity here follows from b>0 and the divisibility of each
positive weight into b. No finite-order assertion is needed for a zero coefficient.

## Proved and sorry left

Closed 1 of the item's original 4 holes:
`AlgebraicGeometry.HilbertCoefficient.commonPowerHilbertMarking`.
Added 0 holes; split off 0 statements. Every added private helper is proved.

Three original holes remain, all attached to `lem-trf-common-power-hilbert-marking`:

- `AlgebraicGeometry.HilbertCoefficient.commonPowerHilbertMarking_charts`.
- `AlgebraicGeometry.HilbertCoefficient.commonPowerHilbertMarking_transform`.
- `AlgebraicGeometry.HilbertCoefficient.hilbertSamuel_le_of_smooth_locally_constant_center`.

The proved first theorem uses the existing named `coefficient_equality_germ` theorem,
whose own proof is still sorry; it remains the existing lower item, without duplication.
This delivery closes one upper hole and adds none.

## No longer needed

Removed redundant proof imports:

- `Sheaf.AlgebraicGeometry.EtaleNearRegularCoordinateFibre`.
- `Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates`.
- `Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`.
- `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientData`.
- `WeilConjectures.Blowup.Complement`.

The first theorem no longer uses `lem-trf-logarithmic-differential-transform` or a separate
`lem-trf-jet-diagram-hilbert-control` application. The formal criterion already states the
intrinsic Hilbert equality, and the private tangent-cone argument proves the power-order
calculation. These nodes, and the coordinate/blowup nodes, remain in the full item's
DAG dependency union where its three unfinished proofs still require them. No module or
node is withdrawn or declared globally unnecessary. The regular datum is already public
through `FormalCoefficientTransformCriterion`.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The initial equality step can use `coefficient_equality_germ`
directly, including nonclosed points, rather than repeating its jet comparison. The order
calculation can use existing regular-sequence and associated-graded declarations directly,
avoiding construction of an auxiliary `MarkedIdeal` merely to invoke product orders.
The global hH bound and the empty-list mark convention are stronger assumptions than the
initial marking theorem needs once the supplied regular datum is available; their binders
are preserved. The other three original proofs are outside this completed partial proof.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
