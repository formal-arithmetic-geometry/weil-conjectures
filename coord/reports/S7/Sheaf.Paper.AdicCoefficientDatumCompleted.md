## What changed

Completed all six remaining proofs in `Sheaf.Paper.AdicCoefficientDatumCompleted`.
The scalar adjunction uses `sheafRingDerivedHomComparison` with the existing ordinary
adjunction and the selected universal scalar derived pair. The scalar complex counit
is invertible by its K-flat computation. Scalar transitions use the existing normalized
coefficient transition and the limit-cone equation. The strict tower is derived from
K-flat resolutions and levelwise quasi-isomorphism preservation. The balancing maps
form a natural isomorphism by the existing naturality theorem; their section formula
proves uniqueness, and their existing cocycle supplies the reassociated equation.

The ordinary functor presentations `completedConstantExtension` and `reductionChange`
are definitionally equal (`adicDatumOrdinaryExtension_eq`). Use the latter consistently
and abbreviate the identical pure tensor section. Package the universal scalar derived
pair in a record, retaining the counit and its universal and computation properties.
The completed ring has the identical inverse-limit body, now a definition that is
locally irreducible; `adicDatumProjection_comp` exposes its cone equation. A named private
interface for passage from homotopy counits to complex counits avoids repeatedly
unfolding its construction. K-flat preservation uses the existing proved theorem
`scalarExtension_preservesKFlat`: functor extensionality identifies the extension of
an existing normalized scalar pair with the specified ordinary functor. Its proof
imports are `ScalarInternalHomAdjunction` (including the private pair-existence helper)
and `ScalarHomExtensionKFlat`; the repeated tensor-cancellation construction is removed.
No adopted source module or target signature changes. The node's proof and dependencies record this route;
its unit route and all dependencies still needed by its other realization are retained.

Adapted the unclaimed `Sheaf.Paper.IntrinsicCompletionCompleted` at the private
`completedKoszulPowerSheaf_kflat` proof. The original line 595, `rw [heq] at h`, failed:
“Did not find an occurrence” of the completedConstantExtension complex in the
reductionChange K-flat assertion. Replace that rewrite and final exact with
`simpa only [← adicDatumOrdinaryExtension_eq, heq] using h`. No public signature or
definition of the consumer changes. The original error is the necessary consequence
of the normalized functor spelling; the scalar equality explicitly transports it.

Adapted the unclaimed `Sheaf.Paper.CompletedFiniteReductionTensorComparison`:
the original consumer exceeded 60 seconds against the changed dependency. Both proof
aliases for E now use reductionChange, matching the exposed counit. In that normalized
proof, original line 143 reported failure to synthesize the residue category's
MonoidalCategory instance. Supply `(C := B)` at `tensorLeftIsoTensorRight` to use the
existing local instance at the named completed-module category. These three proof lines
preserve all public signatures and definitions of the consumer.

The item and all 13 textual consumer modules compile against the new item, with
zero warnings. This includes the two adapted consumers and their dependent checks.
The item compiled in 42.5 seconds; the adapted tensor comparison compiled in
50.4 seconds. The two adapted consumers also contain zero sorries.

On resumption, all three submitted modules compiled without warnings in 18.2, 26.3,
and 30.5 seconds respectively. The first resumed delivery reached server preflight,
which found the newly present `FiniteFreeConstructibleScalarTransport` missing from
the `adicDatumTensorSection` change record. Its `finiteFreeConstantTensor` definition
uses the identical pure-tensor section; that consumer is now listed and checked.
No consumer source change is needed. Its unchanged source compiled against the submitted
item and consumer overlay in 3.8 seconds on resumption.

The definition and presentation changes are recorded separately, with old/new text and
all textual users; target meanings using these definitions reopen the usual statement
review. Change records:

- `coord/changes/s7-adic-datum-completed-adicDatumAdjunction_exists.md`
- `coord/changes/s7-adic-datum-completed-adicDatumBalance.md`
- `coord/changes/s7-adic-datum-completed-adicDatumBalance_cocycle.md`
- `coord/changes/s7-adic-datum-completed-adicDatumBalance_exists.md`
- `coord/changes/s7-adic-datum-completed-adicDatumComplexCounit.md`
- `coord/changes/s7-adic-datum-completed-adicDatumExtension.md`
- `coord/changes/s7-adic-datum-completed-adicDatumExtensionCounit.md`
- `coord/changes/s7-adic-datum-completed-adicDatumExtension_kflat.md`
- `coord/changes/s7-adic-datum-completed-adicDatumModelComplexRestrictionIso_exists.md`
- `coord/changes/s7-adic-datum-completed-adicDatumModelDerivedNormalization.md`
- `coord/changes/s7-adic-datum-completed-adicDatumModelNormalization.md`
- `coord/changes/s7-adic-datum-completed-adicDatumModelReduction.md`
- `coord/changes/s7-adic-datum-completed-adicDatumModelRestriction.md`
- `coord/changes/s7-adic-datum-completed-adicDatumOrdinaryAdjunction.md`
- `coord/changes/s7-adic-datum-completed-adicDatumOrdinaryAdjunction_exists.md`
- `coord/changes/s7-adic-datum-completed-adicDatumOrdinaryReduction.md`
- `coord/changes/s7-adic-datum-completed-adicDatumOrdinaryUnit.md`
- `coord/changes/s7-adic-datum-completed-adicDatumOrdinaryUnit_exists.md`
- `coord/changes/s7-adic-datum-completed-adicDatumRing.md`
- `coord/changes/s7-adic-datum-completed-adicDatumTensorSection.md`

## Proved and sorry left

Closed six of six original holes:

- `AlgebraicGeometry.Scheme.adicDatumAdjunction_exists`.
- `AlgebraicGeometry.Scheme.adicDatumComplexCounit_isIso`.
- `AlgebraicGeometry.Scheme.adicDatumOrdinaryTransition_exists`.
- `AlgebraicGeometry.Scheme.adicDatumTowerDerived_exists`.
- `AlgebraicGeometry.Scheme.adicDatumBalance_exists`.
- `AlgebraicGeometry.Scheme.adicDatumBalance_cocycle`.

Holes added: zero. Sorries remaining in the item: zero. Statements split off: zero.
All added helpers are proved in this module and implement parts of the existing
`def-weil-pbc-adic-coefficient-datum` argument.

## No longer needed

Removed the direct private proof imports
`Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck` and
`Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction`: their required results
are already packaged in the coefficient-datum realization used by the proof. No complete
module or DAG node is withdrawn. The shared node's other realization still uses its
original dependencies, so those dependencies remain recorded.

## Where the brief, the DAG or earlier work was wrong

The scalar-transition, ordinary-adjunction and balancing calculations already exist in
`Sheaf.Paper.AdicCoefficientDatum`; repeating their tensor-generation proofs is unnecessary.
The argument preserves the same mathematical statements. The original completed-ring
abbreviation and expanded scalar selections made elaboration repeatedly inspect the
chosen limit cone and the entire derived-change witness. A local interface for the same
limit and a record for the universal pair repair those expansions. The arbitrary-K-flat
preservation theorem already exists in `ScalarHomExtensionKFlat`; transporting it along
the ordinary functor equality avoids duplicating its total-complex proof. No file is
split, no conclusion weakened, and the compile limit is unchanged.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
