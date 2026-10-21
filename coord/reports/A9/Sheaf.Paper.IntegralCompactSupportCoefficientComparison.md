## What changed

Restored `lean/Sheaf/Paper/IntegralCompactSupportCoefficientComparison.lean` from
`quarantine/Sheaf/Paper/IntegralCompactSupportCoefficientComparison.lean`, as required by
the current rework assignment. Every original declaration and statement is retained.

Repaired the universe inference in `scalarTensorTotal` and its isomorphism theorem by
pinning the existing ordinary monoidal structures to the site's actual universes and
excluding ambiguous imported smallness instances. Change record:
`coord/changes/A9-integral-compact-support-tensor-universes.md`.

Proved scalar shift existence and uniqueness from the universal derived counit and
coherent right-Kan shifts; constructed the tensor model using the native derived
localization tensor; proved identity scalar restriction by its actual section maps.
The compact-support factorization is Mathlib mate pasting. Reduction and further
quotient comparison equations follow by combining the two existing scalar composition
laws and cancelling the ordinary tensor associators. Quotient algebra is checked on
representatives; constant-sheaf naturality and the completed structure-map residue
normalization prove the inverse-image squares. Completed scalar identity/composition
use their unique residue normalization. The finite-Tor natural transformation is
invertible componentwise using the existing integral comparison theorem.

Updated the main node's proof route with the already stated native tensor and coherent
Kan-shift dependencies. The unit route and all unfinished parts of the original plan
are retained. No new public declaration or new node is introduced.

Validation: the complete restored module compiles through `lcompile.py` with exit
code 0 in 22.8 seconds and no warnings.

## Proved and sorry left

Closed 17 of the original 35 named holes. Added zero holes, split off zero
statements. The following names are in `WeilConjectures.PurCompactSupport`:

- `scalarCommShift_existsUnique`.
- `restrictIdentity_existsUnique`.
- `tensorModel_exists`.
- `scalarTensorTotal_isIso`.
- `comparison_factorization`.
- `ramifiedKernel`.
- `finiteChange_square`.
- `projection_square`.
- `comparison_reduction`.
- `finiteDirectImage_eq`.
- `finiteQuotient_square`.
- `ramified_quotient_square`.
- `comparison_quotients`.
- `coefficientPrimeUnit`.
- `completedMap_identity`.
- `completedMap_composition`.
- `comparisonOnFiniteTor_isIso`.

The following 18 original holes remain, with their original source and complete proof
docstrings, on node `lem-pur-compact-support-integral-coefficient-comparison`:

- `comparison_commShift`.
- `comparison_composition`.
- `comparison_identity`.
- `scalarOrdinaryTensor_existsUnique`.
- `scalarOrdinaryTensor_naturality`.
- `scalarTensor_existsUnique`.
- `openComparison_isIso`.
- `ramified_reduction_square`.
- `finiteComparison_isIso`.
- `integralCoefficientComparison`.
- `recordedIdentification_existsUnique`.
- `reductionComparison_isIso`.
- `refinementProperOpen_existsUnique`.
- `comparison_refinement`.
- `refinementComparison_coherence`.
- `comparison_strict_towers`.
- `comparison_projection`.
- `projectionDomain_complete`.

`projection_square`, owned also by `def-sf-open-reduction-coefficient-mate`, is proved.
This delivery completes the assigned restoration/universe repair and proves the named
subresults; it does not claim that the full integral coefficient comparison is proved.

## No longer needed

Removed these unused proof-only imports from the restored module:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `WeilConjectures.RingTheory.FiniteOverCompleteRing`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`.
- `Sheaf.Algebra.Homology.KFlat`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`.
- `Sheaf.Paper.NormalizedDVRTower`.
- `Sheaf.Paper.NormalizedDVREffectivity`.
- `Sheaf.Paper.SfIntegralCompactSupportConstructible`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`.
- `WeilConjectures.Compactification.CategoryBaseChange`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.CompletedProjectionCoherence`.
- `Sheaf.Paper.CompletedPullbackAdjunction`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.DerivedAdjunctionShift`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`.

Their declarations remain in the library, and their nodes remain in the unfinished
proof plan where still required. No whole module is withdrawn or claimed unreachable;
all public imports are retained. No source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The source module is currently quarantined rather than present under `lean/`; its
absence does not withdraw its statements. The current rework row and preserved archive
were used. The archive fails against current instance search because polymorphic
smallness instances admit an unconstrained coefficient universe. Explicit instance
selection repairs the original signed tensor construction without changing its meaning.

The generic native derived tensor and coherent Kan-shift theorem already supply two
pieces of the planned construction. They are reused and recorded in the DAG rather
than restated as new unfinished lemmas. `tools/downstream.py --uses scalarTensorTotal`
cannot resolve the quarantined module, so the consumer audit also searches the archive
and live source trees explicitly (details in the change record).

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
