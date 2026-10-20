## What changed

Proved the strict ordinary quotient transitions and augmentation, constructed the
universal K-flat derived reduction, and descended the normalized strict pullback
comparison. The assigned module now has no `sorry`.

Projection invertibility is decomposed at the mathematical boundary in its proof:
a new theorem supplies the perfect projection formula at one fixed finite
coefficient. The assigned module proves joint conservativity of derived diagram
evaluations, verifies the ordinary balancing and derived normalization hypotheses,
and obtains invertibility of the whole strict projection from that finite result.
The generic completion-mate restatement and the unit route are retained.

The reduction pair is bundled in the existing `DerivedReductionModelData` API.
The augmentation is the explicit universal derived lift; `augmentation_normalized`
and `augmentation_eq_choose` prove its original normalization and equality with
selection from the uniqueness interface. Sharing the abstract counit predicate
avoids repeated unfolding of large concrete functor terms. The new predicate's
specialization is definitionally equal to the original displayed formula (checked
by a separate `rfl` probe). Literal functor choices are related by the unique
counit-compatible universal isomorphism; they are not claimed definitionally equal.

All original public theorem signatures and target signatures are unchanged. The
adopted `lean/WeilConjectures` source tree is unchanged. No module is withdrawn.

## Proved and sorry left

Nine original holes are proved, in namespace
`AlgebraicGeometry.Scheme.OrderedExchange`:

- `quotient_comm`
- `step_existsUnique`
- `reductionModule_additive`
- `reduction_exists`
- `ordinaryAugmentation_existsUnique`
- `augmentation_existsUnique`
- `ordinaryReductionPullInv_isIso`
- `levelPullIso_transition`
- `reductionPullIso_existsUnique`

The tenth original hole, `projection_isIso`, is closed by a one-for-one
decomposition, not counted as a further proof. Its combining proof is complete.
The remaining theorem is
`AlgebraicGeometry.Scheme.ConstantPerfectProjection.evaluation_isIso` in
`Sheaf.Paper.PerfectConstantProjectionEvaluation`, node
`lem-sf-cbc-perfect-constant-projection-evaluation`.
It is exactly `:= by sorry`, with its source and complete proof in words.
There are zero holes in the assigned module and one hole in the added module.
Local declaration accounting: ten holes closed, one added. The sorry ledger
independently computes the targets' import-closure accounting.

The new `reductionData_exists`, representative normalization and augmentation
choice-equality lemmas are proved. All private helpers are proved. No definition
contains `sorry`, and no data is selected from the new unproved theorem.

Validation: the final assigned module compiled in 50.4 seconds and its new
finite-level dependency in 6.0 seconds. All six direct consumers compiled:
`CompletedProjectionCoherence` (12.4 s), `CompletedPullbackUnitTower` (13.6 s),
`CompletedExchangeCoherence`
(6.7 s), `SfCbcExtensionZeroCompletion` (35.0 s), and
`SfCbcCompactSupportCompositionLimit` (10.7 s).
The separate 33.4-second diagnostic check proves by `rfl` that the shared
normalization predicate expands to the original displayed formula, and checks
the public augmentation normalization and choice-equality declarations.
Temporary diagnostic modules and unmodified consumer copies are removed from
the delivery. No compiler error or warning remains in these checks.

## No longer needed

The previously retained unclaimed consumer adaptation `Sheaf.Paper.OrderedExchangeCoefficientComparison` is pruned from this repair packet: the assigned module does not import or use it, and its source is quarantined. Its dead import of `Sheaf.Paper.PbcQbarCompletedPullback` therefore no longer enters the delivery.

Removed these direct imports from the assigned module:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.Paper.CompletedPullbackAdjunction`
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`
- `Sheaf.Paper.ProjectionFormulaTotalization`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`

The native ordinary construction and resolving-class descent do not use those
modules directly. The finite projection piece is recorded explicitly as the new
node, and the native proof uses joint conservativity rather than a faithfulness
claim. No original DAG node or source-library module is declared globally unused:
the publicly retained generic completion-mate theorem still follows the original
route. No `deleted.txt` is needed.

## Where the brief, the DAG or earlier work was wrong

The existing generic totalization theorem has equal object and morphism site
universes. It cannot directly instantiate on the original small pro-etale site,
whose object and morphism universes differ. Its independent-universe abstract
tensor-adjunction total maps remain ingredients for the new finite-level result;
no universe equality or completed/discrete coefficient identification is assumed.
The existing completed-ring perfect projection theorem also has different
coefficient rings from this constant-A construction.

The expanded counit normalization and nested choices repeatedly exceeded the
60-second compile limit. The bundled universal pair, explicit universal lift and
shared normalization predicate repair those interfaces without raising the limit
or splitting a proof to obtain a shorter compile. The finite-level lemma is
separate because it is the source's one-coefficient perfect projection argument;
it does not include the parent's joint-conservativity step or its conclusions
at all finite indices.

## New nodes

`lem-sf-cbc-perfect-constant-projection-evaluation` records the finite perfect
coefficient projection formula for arbitrary normalized derived models of an
ordinary strict diagram. The specified index is the only constrained component;
other components and transitions are arbitrary. The proof uses a bounded
finite-projective coefficient model, exact constant realization, K-flat model
normalization, K-injective evaluation, and the signed finite-total projection
inverse. Edge cases checked in words: zero coefficient ring, I=A, I=0, index zero
(exponent one), rank zero, and unbounded input complexes. The parent applies this
single-index statement and proves the passage to the whole tower in Lean.
Four search records in the new node cover the three required kinds: LeanSearch,
Loogle/LeanFinder, and direct grep of the Mathlib source. Its public helper data are
explicit constructions, and it has one named remaining proof obligation.

Change records:

- `coord/changes/G4-orderedExchange-reduction.md`
- `coord/changes/G4-orderedExchange-reductionCounit.md`
- `coord/changes/G4-orderedExchange-reductionComplexCounit.md`
- `coord/changes/G4-orderedExchange-augmentation.md`
- `coord/changes/G4-orderedExchange-ReductionPullNormalized.md`

- `coord/changes/G4-orderedExchange-limitComplexUnit.md`

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
