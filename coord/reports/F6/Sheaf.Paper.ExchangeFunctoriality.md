## What changed

Proved nine existing holes in `Sheaf.Paper.ExchangeFunctoriality`, preserving all existing
public declaration signatures and definition bodies. Added proved private helpers for linearity,
open-extension and proper-image preservation, and generator-tuple independence. The finite-extension
exchange is constructed by scalar localization of the actual completed compact-support exchange.
Its identity and pasting equations are images of the existing integral equations. Updated
`fix-lem-exchanges`, proof step 16 and its dependencies, to record these helper proofs; the
remaining top-level plan is retained. No source-library module or target was changed.

## Proved and sorry left

Closed 9 of the original 10 holes, with zero new holes and zero split-off statements. All nine
names below have prefix `AlgebraicGeometry.Scheme.LiftedCbc.` and belong to node
`fix-lem-exchanges`:

- `cbcCompactSupportSourceLift_additive`
- `cbcCompactSupportTargetLift_additive`
- `cbcCompactSupportSourceLift_linear`
- `cbcCompactSupportTargetLift_linear`
- `finiteExtension_compactSupportBaseChange`
- `finiteExtension_cbcComplete`
- `finiteExtension_compactSupportBaseChange_identity`
- `finiteExtension_compactSupportBaseChange_horizontal`
- `finiteExtension_compactSupportBaseChange_vertical`

The sole remaining hole is `WeilConjectures.exchangeFunctoriality`, node `fix-lem-exchanges`.
This delivery is partial: it does not claim that the top-level exchange comparison or the entire
item is proved. In particular, identifying `sbcExchangeApp` with `pbcActualCompletedExchange`
through the prescribed model isomorphisms, and proving its specified completed mate laws, remain
unfinished. No arbitrary replacement comparison was substituted.

## No longer needed

Removed the following direct private imports, none of which the nine completed helper proofs
need directly:

- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.Paper.RefinementComparisonIsomorphism`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.CompletedCoefficientPushforwardComparison`
- `Sheaf.Paper.SfCbcCompactSupportCompositionLimit`
- `Sheaf.Paper.SfCbcExtensionZeroCompletion`
- `Sheaf.Paper.CompletedPullbackAdjunction`
- `Sheaf.Paper.ProEtaleConstantReductionTower`
- `Sheaf.Paper.ProperOpenTowerComparison`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.StrictTowerExchangeMateNormalization`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `WeilConjectures.Compactification.NagataCompactification`

No module is withdrawn, and no DAG node is declared globally unnecessary. These imports belonged
to the broader unfinished top-level plan; its dependencies are retained. The completed helpers
reuse the existing compact-support coherence interface instead of reproving its strict-tower
argument. Public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The module contains ten proof holes, not just the top-level theorem. Its module-owned
`LiftedCbc` helpers can be proved from the current complete compact-support interface without
identifying the two completed ordinary-exchange models. That model identification is still a
separate unfinished argument in the top-level theorem. Existing statements were neither weakened
nor disputed. The derived-adjunction linearity route unfolded a large direct-image construction;
the retained proof instead derives linearity from the existing module pullback linearity proof.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
