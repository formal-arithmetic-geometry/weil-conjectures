## What changed

Replaced `WeilConjectures.derivedPullbackTensorIso`'s final hole with an explicit
assembly of its unchanged 26 conjuncts. Existing finite, integral and rational
constructions, reduction, associativity, braiding, quotient, scalar and evaluation
results supply their respective conjuncts. The integral naturality proof reflects
the system comparison's naturality along faithful coherent reduction; the rational
natural isomorphism uses the existing public
`OperationsScalarLocalization.bilinearComparison_existsUnique`.

Added the proved `Sheaf.Paper.CommonStagePullbackTensorNaturality`. Two input
morphisms are represented at a common field containing the tensor stages. The
actual comparison and operation representative formulas reduce naturality to its
rational square, conjugated by endpoint comparisons. No injectivity of scalar
extension is assumed. The main module uses this proof with `NatIso.ofComponents`.

Also closed common-stage associativity with its explicit finite-stage representative
argument. A lower dependency now exposes `rationalAssociator_natural`, whose proof
reuses the existing private integral and rational calculations of
`CommonStageTensorLineCoherenceNaturality`. Its dependency on the constraints avoids
an import cycle through that consumer's public theorem. Faithful reduction proves
integral naturality, and induction on three scalar tensor arrows proves rational
naturality. No new hole is used for these naturality statements.

The remaining composition and unit diagrams are separated into
`Sheaf.Paper.PullbackTensorCompositionCoherence` and
`Sheaf.Paper.PullbackTensorUnitCoherence`. Each has one public named theorem, its
own node, and a complete source argument in its docstring. These are strictly
smaller structural parts of the parent, not renamed copies of it.

During verification, the earlier D2 split was reverted after its global build
failed on the obsolete private helper `semilinearTensorIso_localize`. The first
delivery therefore stopped at missing source imports and pushed nothing. This
packet is rebased onto the resulting live source. It factors its 59 existing
constraint declarations into `Sheaf.Paper.DerivedPullbackTensorConstraints`,
publicly re-exported by the item. Their signatures and every data definition are
verbatim. The six existing holes in these constraints are preserved.

The existing proved generic reduction calculations are factored into
`Sheaf.Paper.PullbackTensorReductionCalculus`, with the new proved public theorem
`WeilConjectures.reducedComparison_natural`. It composes the tensor and pullback
reduction isomorphisms, uses their naturality and the normalized component square,
cancels an isomorphism, and reflects equality by faithfulness. Proof imports stay
private; the parent publicly re-exports the unchanged constraint declarations.
The change record is `coord/changes/A4-pullback-tensor-constraint-factoring.md`.

The seven delivered modules have compiled through `lcompile.py`. The main item
and the generic calculus module compile without diagnostics after the final
associativity calculation. The three public theorem signatures in the item are
byte-identical to the restored live source. All 64 direct importers were checked
against the factored API, using unchanged copies which have now been removed.
Fifty-two passed ordinary compilation. `FiniteTateSourceStructuralCoherence`
initially took 62 seconds; diagnostic profiling then passed at 37.5 seconds against
this packet and 39 seconds against the baseline, with matching profiles (48.4 and
50.6 seconds of cumulative parallel kernel checking). Its only temporary changes
were the two profiler options; these were removed. No consumer is delivered.

The following eleven unchanged consumers exceeded the time limit both against
this packet and against the published baseline (exit 124 in each environment).
No consumer reported a type or signature error. These pre-existing timing failures
remain a limitation of the compatibility check, rather than claimed passing checks.
The current shared sources were compared with all 64 verification copies before
the copies were removed. The concurrently updated `ConstantPurityFrobeniusSquare`
was refreshed and checked again in both environments.

| Consumer in `Sheaf.Paper` | Packet | Baseline |
| --- | --- | --- |
| `CommonStageTensorBraidingNaturality` | time limit | time limit |
| `CommonStageTensorLineCoherenceNaturality` | time limit | time limit |
| `CommonStageTensorRightUnitorNaturality` | time limit | time limit |
| `ConstantPurityFrobeniusSquare` | time limit | time limit |
| `DerivedAutomorphismHomEvaluation` | time limit | time limit |
| `FiniteClopenDerivedDecomposition` | time limit | time limit |
| `GeometricFrobeniusInternalHomComparison` | time limit | time limit |
| `PodReindexingHomCoefficientDescent` | time limit | time limit |
| `RationalRealizationTensorComparison` | time limit | time limit |
| `RelativeProductBaseChangeFactorSquares` | time limit | time limit |
| `SemilinearFieldOperationLifts` | time limit | time limit |

Four existing definition nodes also have their Lean module/file attachments
updated to the support module: `def-pod-integral-tensor-constraints`,
`def-pod-rational-common-pullback-composition`,
`def-sf-rational-common-tensor-symmetries`, and
`def-a1-common-stage-coefficient-unit`. Their statements and dependencies are
unchanged. The new unit subclaim cites the comprehensive constraints record
directly; redundant references to its older overlapping definition records
were removed after server preflight identified a new DAG cycle. This is a
metadata correction and changes no Lean source. Additional transitive textual
users are now included in the change record.

## Proved and sorry left

The rebased live item has eight original holes. Closed two:
`WeilConjectures.derivedPullbackTensorIso` and
`WeilConjectures.canonicalCommonStagePullbackTensor_associative_spec`
(both recorded by `lem-pur-derived-pullback-tensor-iso`). Added two strictly smaller
structural holes. This is a decomposition, not a net hole reduction: eight original
holes become eight holes across the delivery, including the six moved constraints.

Also proved `WeilConjectures.commonStagePullbackTensor_naturality`
(`lem-pur-common-stage-pullback-tensor-naturality`),
`WeilConjectures.reducedComparison_natural`
(`lem-pur-reduced-pullback-tensor-naturality`), and
`WeilConjectures.rationalAssociator_natural`
(`lem-pur-rational-pullback-tensor-associator-natural`), with their private helpers.
The live common-stage braiding proof and all other existing proofs are retained.

Every remaining hole is listed here, in namespace `WeilConjectures`:

- `pullbackTensorCommonComposition_existsUnique`, moved unchanged.
- `pullbackTensorCommonAssociator_existsUnique`, moved unchanged.
- `pullbackTensorCommonBraiding_existsUnique`, moved unchanged.
- `pullbackTensorRationalScalarUnit_existsUnique`, moved unchanged.
- `pullbackTensorCommonLeftUnitor_existsUnique`, moved unchanged.
- `pullbackTensorCommonRightUnitor_existsUnique`, moved unchanged.
- `pullbackTensorCompositionCoherence`, new split,
  node `lem-pur-pullback-tensor-composition-coherence`.
- `pullbackTensorUnitCoherence`, new split,
  node `lem-pur-pullback-tensor-unit-coherence`.

The six moved statements belong to
`lem-pur-derived-pullback-tensor-constraints`. The item has zero remaining holes;
there is no hole in a definition. Imported dependencies keep their recorded holes.

## No longer needed

The proof uses the public scalar-localization comparison, with no private helper
import from `DerivedPullbackTensorHom`. The reverted
`LocalizedTensorAssociatorNaturality` module is not imported: the needed rational
associator naturality is extracted from existing proved private calculations into
`RationalPullbackTensorAssociatorNaturality`. The original six proof imports of
the live item now belong to the constraint file whose proofs use them.

The parent's proof no longer directly follows the old resolution/reconstruction
route nodes `lem-pc-kflat-resolution`,
`lem-pur-finite-derived-comparison-normalization`,
`lem-pur-integral-operations-preserve-constructible`,
`lem-pur-integral-operations-scalar-extension`,
`lem-pur-normalized-completed-operation-models`,
`lem-pur-normalized-reconstruction-adjunction-calculus`,
`lem-sf-derived-complete-legacy-comparison`, `lem-weil-proetale-dbc-triangulated`,
`prop-weil-pbc-proetale-constant-exact`, or `def-weil-constant-coefficient-objects`.
The existing constraint constructions and their private proof imports still use
these results. The completed quotient and bilinear descent nodes support the
remaining structural subclaims.

No module is claimed globally pruned or withdrawn. All live public imports of
the item are preserved; its new constraint import preserves the moved API.

## Where the brief, the DAG or earlier work was wrong

The original parent hole is largely assembly of constructions already present.
The two new structural statements isolate the remaining composition and unit
arguments. Naturality at a common stage needed a real representative calculation,
which is now proved rather than bundled into an assertion of a natural isomorphism.

The shared source changed during this session: its initial D2 split had one hole
in the item and six in its support module. After the rollback the live item again
had eight holes and the two support source files were absent. The first delivery
caught this and pushed nothing. This packet uses the restored live source and
records the correct count of eight. The rolled-back common-stage associativity
proof depended on an unavailable generic associator helper. A subsequent search
found the needed proved private naturality calculation in a direct consumer.
Extracting it to a lower dependency closes the live associativity hole without
restoring the unavailable module or importing the consumer in a cycle.

The current blueprint's `def-weil-derived-pullback-tensor-hom` treats higher
coefficients uniformly as condensed coefficients, expressly distinguishing them
from constructions by finite reduction. The assigned Lean interfaces still
prescribe completed/rational/common-stage constructions. This delivery preserves
their statements and definitions rather than silently reinterpreting them. The
new subclaims use the recorded parent structural argument and Stacks 07A4/0941.

Edge cases checked at statement level: identity scheme maps give the same unit
and composition equations; zero inputs require no nonzero Hom assumptions; no
finite-type, separation or Tor-dimension hypothesis is added. The common-stage
proof accepts arrows initially represented at different fields. Unit uniqueness
means uniqueness under both unitor equations, not uniqueness of any isomorphism
of the unit objects. The generic naturality theorem needs only faithful reduction.

## New nodes

`lem-pur-common-stage-pullback-tensor-naturality`: proved descent of the prescribed
comparison's naturality from all rational stages.

`lem-pur-pullback-tensor-composition-coherence`: the three higher composition
squares, one remaining named theorem.

`lem-pur-pullback-tensor-unit-coherence`: the three higher unit comparisons and
both unitor equations, one remaining named theorem.

`lem-pur-reduced-pullback-tensor-naturality`: proved reflection of comparison
naturality through a faithful reduction and normalized component equation.

`lem-pur-derived-pullback-tensor-constraints`: the 59 unchanged declarations moved
from the current live parent, with their six existing holes and source arguments.
The factoring record is `coord/changes/A4-pullback-tensor-constraint-factoring.md`.

`lem-pur-rational-pullback-tensor-associator-natural`: proved naturality of the
actual normalized rational associator on three arrows, using faithful integral
reduction and scalar tensor induction. The source consumer is unchanged.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
