## What changed

Proved `AlgebraicGeometry.Scheme.pbcConeIndependence` with its original signature,
definitions, universes and visibility. The proved generic theorem
`CategoryTheory.StageSystem.coneIndependenceOfExact` assembles its four clauses:
scalar extension, comparison of representatives, finite-stage cone uniqueness,
and equivalence of distinguishedness witnesses.

The proof constructs the endpoint-associator triangle isomorphism explicitly,
uses the existing representative equality criterion to find an agreement field,
and applies Mathlib `isoTriangleOfIso₁₂` there. It carries that isomorphism to the
pair category by mapped triangles, proves the endpoint comparison equations from
the stage-system cocycle, and composes witnesses with the comparison or its inverse.

Private proved helpers establish exactness for the actual coefficient transitions:
scalar restriction is an exact derived functor, its left adjoint is exact by
Mathlib `Adjunction.isTriangulated_leftAdjoint`, and the integral restriction is
exact through its fully faithful inclusion. The published integral-image criterion
for stage triangles and the shift-compatible integral/rational comparison then
prove rational scalar exactness. Transition-identification shift compatibility
is proved directly from associator shift coherence. No pair-category
pretriangulation or downstream Verdier theorem is used.

Added the proof-only Mathlib triangulated-adjunction import. The assigned
Lean module, its existing DAG node, and the required change record are delivered;
no consumer adaptation or statement/definition change is needed. The DAG proof now records the exactness
assembly and the mapped-triangle comparison used by the Lean proof.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.pbcConeIndependence`
(node `prop-weil-pbc-cone-independence`). Proved
`CategoryTheory.StageSystem.coneIndependenceOfExact` and all private helpers.
The delivered module has zero `sorry`; zero holes added and zero statements split off.
Existing dependencies retain their own separately assigned holes.

Validation: the complete item compiled cleanly through `lcompile.py` against the
current library. Delivery dry-run/preflight checks are run on the final files.

## No longer needed

Removed direct proof imports `Sheaf.Paper.PbcScalarExtension`,
`Sheaf.Paper.CommonStageCalculus`, and `Sheaf.Paper.FiniteStagePairCategory`.
Their relevant declarations and interfaces are already available through the
unchanged public import `Sheaf.Paper.PbcCommonStageCones`; their DAG nodes remain
needed. No entire module or original DAG dependency is pruned.

The previous attempt's proposed `Sheaf.Paper.PbcVerdierAxioms` import and reverse
import removal are unnecessary: this proof derives the two finite-stage inputs
it needs directly. No change to that module is delivered. The superseded change
record is retained only in the sandbox scratchpad, outside the delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier report described an import-direction repair which is absent from
the retained final Lean code. Importing PbcVerdierAxioms for finite-stage inputs
would create a source cycle, since that downstream module imports this item.
The retained proof avoids the cycle completely by proving exactness from the
existing scalar adjunction, integral inclusion, and rationalization comparison.
The previously reported adaptation-gate failure therefore no longer applies.

The scalar-extension node's `pbcStageExact` uses a different stage presentation
from the actual `pbcScalarSystem`, so it cannot simply be supplied by instance
search here. The private exactness helpers bridge the actual published stages
without changing their definitions or assuming the pair-category conclusion.
The six-step cone-independence argument and current blueprint route are retained.

Change record: `coord/changes/P5-pbc-cone-independence-proof-context.md`.
It documents the added proof contexts and proved generic helper, with the complete
consumer list; all existing signatures and definitions remain identical.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
