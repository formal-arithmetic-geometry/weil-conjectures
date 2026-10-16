# localFinitePresentation_comap and localFinitePresentation_pullback

## Reason

The nonempty support proof needs local finite presentation before choosing the trivial
stratification. The existing public API exposes constructible pullback, while these two
already proved local finite presentation transport lemmas were private. Expose precisely
these lemmas. The module was unclaimed when this adaptation was made; the launcher's
2026-10-12 adaptation rule authorizes changing an unclaimed module.

No definition or existing public statement changes, so target meanings do not change.
This is a visibility addition, with no forced adaptations of another group's module.

## Old

```lean
private lemma localFinitePresentation_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented S ((Mod.comap φ).obj M)
```

```lean
private lemma localFinitePresentation_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] {M : Mod _ R}
    (hM : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented ((f)^*[Ab.{u + 1}].obj R)
      (((f)^*[Ab.{u + 1}].mapMod R).obj M)
```

## New

```lean
lemma localFinitePresentation_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented S ((Mod.comap φ).obj M)
```

```lean
lemma localFinitePresentation_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] {M : Mod _ R}
    (hM : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented ((f)^*[Ab.{u + 1}].obj R)
      (((f)^*[Ab.{u + 1}].mapMod R).obj M)
```

## Users

The complete downstream list from `tools/downstream.py --uses` is below. Its textual
use scan found the two names only inside the defining module; existing downstream
modules therefore need no edits. The two new direct users are included as well.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | B3 | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | B3 | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | unclaimed | Expose two existing, proved local finite presentation lemmas. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedConstructibleOneStep | J1 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | G2 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | D3 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedLocalPresentationPullback | G4 (new) | Uses the newly public local finite presentation API. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | E3 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | G1 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | G4 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | G4 (new) | Uses the newly public local finite presentation API. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | A4 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | E4 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | F1 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralMatrixPivotCover | C3 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralResidueExchange | C2 | No statement or definition changes; visibility addition only. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | No statement or definition changes; visibility addition only. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No statement or definition changes; visibility addition only. |
| TargetsCheck | unclaimed | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A2 | No statement or definition changes; visibility addition only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No statement or definition changes; visibility addition only. |

## Status

landed 20261016T052146-L-3987657 2026-10-16 (merge of deliver/G4/Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed)
