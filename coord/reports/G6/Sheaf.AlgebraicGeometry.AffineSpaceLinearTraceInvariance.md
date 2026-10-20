## What changed

Replaced the one hole in
`AlgebraicGeometry.Etale.affineSpaceLinearTraceInvariance` with a complete Lean
combination of universal-action specialization, connected-fibre identity detection,
and cancellation. Its statement is unchanged. The blueprint's universal-GL,
ordinary-sheaf and compact-support route is retained.

Moved the nine existing concrete definitions, preserving their names, signatures,
visibility and definitionally equal bodies, to `Sheaf.AlgebraicGeometry.AffineLinearTraceAction`, publicly
re-exported by the original module to avoid a cycle. Proved
`AlgebraicGeometry.affineTraceLinearMap_isPullback` from coordinate formulas: the
matrix composition law and the inverse matrix give its actual Cartesian square.
The identity inverse-image object in `affineLinearTraceAction` is now explicit; this
preserves the construction while avoiding expansion of the compactification functor.
Proof-local irreducibility keeps these comparison definitions folded.

`AffineLinearUniversalAction` uses the existing source-library relative determinant-open,
constructs the universal invertible matrix, proves Noetherianity and invertibility of N,
and defines the existing source and action as convenient wrappers. The proved
`linearUniversalMatrix_specialize` says that a matrix section evaluates the universal
matrix to exactly the supplied matrix.

`AffineLinearActionRigidity.linearAction_eq_id_of_identitySection` is proved. The source
is independent of normalized projective-line data. Any one witness of
`exists_affineSpaceTopTrace` identifies it with the constant complex, hence makes it
invertible. The existing source-library `exists_isPreconnected_glOne` and
`eq_id_of_leftDerivedUpperStar_map_eq_id_of_isInvertible` then detect the identity
along the closed identity section. These source lemmas use ordinary sheaf maps and
connected-fibre geometry; no supported Kummer class or zero-section purity is used.

The original theorem applies the proved family theorem, proves its universal
action is identity by this detector, and specializes to g. Cancellation of its
comparison isomorphism proves that the action of g itself is identity, hence preserves
the supplied trace for every D, without comparing choices of normalized traces.

The retained unchanged VectorBundleIntegration consumer check passed against the
relocation; names and public imports are preserved. The resumed session compiled all
six modules cleanly in import order against the current published build.

## Proved and sorry left

The delivery replaces the original hole in
`AlgebraicGeometry.Etale.affineSpaceLinearTraceInvariance`
(node `lem-amb-linear-trace-invariance`). The submitted source files contain zero sorries.
No hole is split off. The new family and exchange theorems have explicit proofs,
using the existing library statements about unbounded exchange pasting and identity.
Existing dependency declarations are not changed by this delivery.

The subsidiary results are `affineTraceLinearMap_isPullback`,
`affineTraceMap_isPullback`, `affineTraceLinearMap_one`,
`affineTraceLinearMap_baseChange`, `linearUniversalMatrix_specialize`,
`linearUniversalInvertible`, `linearAction_eq_id_of_identitySection`,
`affineLinearExchange_paste`, `affineLinearExchange_action`,
`affineLinearExchange_action_naturality`, `affineLinearAction_one`, and
`affineLinearAction_family`. All names except the geometric ones are in
`AlgebraicGeometry.Etale`; the geometric ones and universal matrix are in
`AlgebraicGeometry`.

The resumed session repaired the costly coefficient-coherence proof by applying a proved
abstract diagram of isomorphisms to the three inverse-image associativity equations.
The final clean compile took 1.6 seconds for the relocated definitions, 24.1 for
exchange coherence, 8.3 for the universal matrix, 26.7 for the family theorem,
18.1 for rigidity, and 7.6 for the original theorem. All six modules compiled
without warnings, and the packet contains zero textual holes. The required dry run
passed (CODEX review). Its appended axiom probes timed out for
`AffineLinearActionFamily` and `AffineLinearActionRigidity`; the delivery tool
explicitly schedules those probes to run again at merge. No axiom failure was
reported. These probe timeouts did not affect the clean module compiles above.

## No longer needed

No existing library module is claimed pruned globally from the targets' closure.
The proof no longer needs explicit residue-field scalar functions or a new model of
the determinant-open: it reuses the existing relative determinant-open and the proved
source identity detector. The unsubmitted earlier modules
`AffineLinearActionResidueScalar`, `AffineTraceHomResidueExt` and
`AffineLinearParameterConnected` are unnecessary, and their unsubmitted nodes are
omitted. None of these was ever landed, so this does not withdraw library files.

The original proof-only imports removed from the item or relocated definition module:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `WeilConjectures.Compactification.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Sheaf.Paper.ConstantSheafSectionsLocallyConstant`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `Mathlib.CategoryTheory.Sites.LocallyBijective`
- `Mathlib.Topology.LocallyConstant.Basic`
- `Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange`
- Redundant proof import from the new family module:
  `WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence`

The former proof dependency `lem-amb-compact-action-base-change` and its module
`Sheaf.AlgebraicGeometry.CompactSupportActionBaseChange` are no longer used by this
proof: the proved exchange equations operate directly in the unbounded model.
The explicit degree-zero full-faithfulness, constant-sheaf section and connected-map
steps are discharged inside the existing source identity detector, rather than
restated as affine-trace lemmas. The finite-type, affine-spectrum, fibre-product and
projective compactification geometry remains available through the constructions
and compact-support API; it is not claimed pruned globally.

FiniteType is used in the new universal construction. The family theorem instead uses
`UnboundedEtaleCompactSupportComparisons`, the existing API for the same unbounded
compact-support exchange, through the proved `AffineLinearExchangeCoherence` module. Geometry and ordinary-sheaf connectedness are now inside the source-library detector. The existing public imports accompany the relocated
definitions unchanged. The parent's obsolete top-level tool approvals are removed:
compact-support base change, finite Tate pullback and projective compactification are
now used by the family node; constant-sheaf detection is supplied by the proved source
API. None is claimed mathematically unnecessary globally.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The earlier scalar reduction needlessly required a
comparison of arbitrary supplied normalized traces. Showing the action itself is the
identity avoids that comparison. The source library already contains the exact
connectedness and invertible-object detection argument required, so constructing
another determinant-open and another ordinary-sheaf detector adds unnecessary work.

The family compatibility does not follow by directly applying the generic
bounded-below compact-support action theorem: its actual action is transported through
specified comparisons to an unbounded coordinate tower. The resumed proof uses the
existing unbounded exchange pasting and identity declarations. Inverse-image
associativity and naturality prove the coefficient coherence equations explicitly.
The final theorem then uses connectedness, the top-trace isomorphism and identity
detection, followed by cancellation.

## New nodes

`def-amb-affine-linear-trace-action`: relocated definitions and proved Cartesian
certificate, preserving the existing public interface.

`def-amb-affine-linear-universal-action`: existing relative determinant-open,
constructed universal matrix, its proved specialization, Noetherianity and N-invertibility,
and wrappers for the actual trace source and matrix action.

`lem-amb-affine-linear-action-family`: identity restriction and specialization
compatibility of the universal action, with explicit proofs.

`lem-amb-affine-linear-action-rigidity`: proved identity detection from the identity
section for endomorphisms of the universal affine trace source.

`lem-amb-affine-linear-exchange-coherence`: horizontal pasting in the left-derived
inverse-image model and equivariance after coefficient transport, proved from the
existing unbounded compact-support exchange and inverse-image coherence APIs.

Change record: `coord/changes/affine-linear-trace-action-relocation.md`.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
