## What changed

Replaced the `rationalThickEvaluation` hole by a complete Lean assembly proof.
The integral construction (original DAG Steps 1–7 and 9) and rational descent
(Step 8) are two new, independently usable intermediate statements. Neither states
the original theorem: the first has no rational structures or locus conclusions;
the second assumes arbitrary integral exact linear comparison data and has no
completeness, normalization, coefficient or closure conclusion.

The assembly evaluates the rational comparison square to identify the actual
`evaluationLocus` with `alphaQ.isoLocus.unop`. The already proved source-library
`NatTrans.isoLocus` instances give triangulated closure. Applying retract stability
to the opposite retract proves rational retract closure, hence closure under
isomorphisms. Finite products are in a triangulated replete subcategory; the
finite-biproduct colimit/limit isomorphism proves finite coproduct closure,
including the empty family. The coefficient component is invertible under `q`.

Validation: the item and both split modules compile, as does the data module.
`RationalSliceCompletedEvaluation`, `SitePerfectDualizableHom` and
`SfPackageCoefficientDomains` compile against their new public re-export.
`CoefficientDualModelTransport` reached the fixed 60-second limit both with this
packet and against the unchanged published baseline (with profiling enabled);
no compiler diagnostic preceded either timeout. Its source is unchanged and no
forced adaptation is claimed.

Moved the scalar and evaluation data verbatim to `RationalEvaluationData` with a
public re-export, so the two new modules can import them without an import cycle.
Updated both ownership records and the main proof DAG. No source-library file,
target signature, definition body or consumer is changed.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.IntegralOnSlice.rationalThickEvaluation`.

Added two holes, each the entire proof of one public named theorem in its own module:

- `WeilConjectures.IntegralOnSlice.integralCompletedEvaluation`, node
  `lem-sf-integral-completed-evaluation`, module `Sheaf.Paper.IntegralCompletedEvaluation`.
- `WeilConjectures.IntegralOnSlice.completedEvaluation_rationalDescent`, node
  `lem-sf-completed-evaluation-rational-descent`, module
  `Sheaf.Paper.CompletedEvaluationRationalDescent`.

This is a decomposition: one upper hole closed, two strictly smaller holes added,
net -1. The actual remaining packet hole count is two; the item module has zero.
The scalar-chain, scalar-linearity and shift-linearity proofs were already proved
and are moved verbatim; they are not newly closed holes.

## No longer needed

The assembly no longer needs the following direct private imports. Their mathematics
is retained in the integral/descent nodes where applicable; this does not withdraw
or claim to prune their modules from the whole target closure:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.WeilCompletedTensorReflector`
- `Sheaf.Paper.DerivedCompleteUnrestricted`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.IntegralDerivedOperations`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

No former public import is lost: all are re-exported through the data module.
The original main-node tool approvals other than `lem-sf-triangle-morphism-iso`
are removed as direct uses: their original steps and dependencies remain in the
new integral/descent nodes. No module or DAG node is withdrawn. No unit route is bypassed. All original
proof-dependency steps remain in the two split nodes, except the final categorical
closure is now supplied by the proved source-library API and Mathlib's biproducts.
The original direct proof-dependency edges of the main node are replaced by its
two genuine intermediate steps and the triangle-morphism lemma.


Original proof-dependency edges removed from the main node (none withdrawn globally):

- `lem-weil-l-adic-extension-integers-dvr`: retained in integral step.
- `def-pur-localized-ringed-site`: retained in integral step.
- `lem-weil-pbc-constant-completion-equivalence`: retained in integral step.
- `lem-weil-pbc-ringed-koszul-completion-reflector`: retained in integral step.
- `def-weil-derived-complete`: retained in integral step.
- `def-pc-kflat-complex`: retained in integral step.
- `lem-weil-pbc-site-derived-tensor-descent`: retained in integral step.
- `lem-pur-kflat-change-of-rings`: retained in integral step.
- `def-pur-integral-derived-operations`: retained in integral step.
- `lem-pc-kflat-closure`: retained in integral step.
- `lem-pc-tensor-mapping-cone-iso`: retained in integral step.
- `def-pc-sheaf-restrict-scalars`: retained in integral step.
- `lem-weil-pbc-ringed-strict-tower-homotopy-limit`: retained in integral step.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`: retained in integral step.
- `lem-weil-linear-abelian-derived-category`: retained in integral step.
- `lem-sf-ringed-rhom-derived-complete`: retained in integral step.
- `lem-sfb-ringed-site-duality-maps`: retained in integral step.
- `def-pur-hom-complex`: retained in integral step.
- `def-pc-tensor-complex-sheaves`: retained in integral step.
- `lem-pc-kflat-resolution`: retained in integral step.
- `def-pur-kinjective-complex`: retained in integral step.
- `prop-pur-kinjective-resolutions-exist`: retained in integral step.
- `def-pur-derived-internal-hom`: retained in integral step.
- `lem-weil-pbc-kinjective-hom-derived`: retained in integral step.
- `def-weil-linear-scalar-localization`: retained in descent step.
- `lem-weil-linear-scalar-localization-triangulated`: retained in descent step.

## Where the brief, the DAG or earlier work was wrong

The planned internal-Hom exactness module has a same-universe theorem, while this
item has independent site and coefficient sizes. The later independent-universe
shift module supplies the normalized target shifts, but does not by itself state
all the contravariant exactness, coefficient-linearity and reflector compatibility
needed here. Likewise the published completion reflector specializes a different
completion presentation; passing to the actual slice quotient tower is a real
comparison step. The split preserves those tasks explicitly rather than treating
them as definitional equality.

The source library already proves `NatTrans.isoLocus` triangulated/retract closure,
which the old DAG searches had not found. This replaces the proposed handwritten
rational retract inverse and triangle argument, preserving their mathematical content.
No statement has been weakened or disputed. Edge cases checked: zero M; empty
finite diagram; arbitrary integral source; global site and an actual over-site;
nonintegral rational retracts. The integral coefficient component is invertible
only under the retained completeness hypothesis.

## New nodes

`lem-sf-integral-completed-evaluation` isolates original Steps 1–7 and 9: construction,
linearity, exactness, completeness, normalization, shifts and the coefficient unit.
It retains the original sources and step dependencies and supplies a full proof in
words. No rational triangulation or thick-locus assertion is included.

`lem-sf-completed-evaluation-rational-descent` isolates original Step 8. Given integral
exact linear functors and their shift-compatible comparison, scalar fractions extend
the functors and comparison, and the specified image triangles give exactness.
It includes no statement about evaluation invertibility or locus closure.

LeanSearch, LeanFinder and Mathlib grep were run for both assertions and recorded
from `searches.jsonl`; generic localization tools were found, with no exact actual
completed-coefficient theorem. Blueprint searches found no duplicate assertion.

Change record: `coord/changes/W3-rational-evaluation-data-extraction.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
