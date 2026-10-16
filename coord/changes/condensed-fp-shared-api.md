# Shared finite-presentation transport helpers

## Reason

Repair the landing refusal for repeated `fp_iff_of_iso` and `fp_map` proofs.
The existing declarations are private, so an import alone cannot reuse them.
Make the original, already-proved lemmas public in place, together with their
scalar-extension specialization `fp_extend`. Remove their duplicate proofs
and the duplicate regular-module construction from the parent. Both the parent
and the matrix theorem use proof-only imports of the original module.

`Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars` is unclaimed at the
repair check. Its theorem statements and proof bodies remain unchanged; only
these three visibility modifiers change. No definitions or target types change.

## Old

The declarations are in `AlgebraicGeometry.ProEtale`, with the displayed local
variable context applying to `fp_extend` (the other two state all binders).
All three proofs are already complete.

```lean
private lemma fp_iff_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) : Mod.IsFinitelyPresented R M ↔ Mod.IsFinitelyPresented R N

private lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M)

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [IsCommMonObj S] in
private lemma fp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M)
```

## New

The same declarations and proofs, with public visibility under the existing
`@[expose] public section`:

```lean
lemma fp_iff_of_iso {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) : Mod.IsFinitelyPresented R M ↔ Mod.IsFinitelyPresented R N

lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) [MonObj R] [MonObj S]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) S)
    [F.Additive] [PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular S)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented S (F.obj M)

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
omit [IsCommMonObj S] in
lemma fp_extend
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M)
```

## Users

| Module | Group holding it | Effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars | unclaimed | Three existing proved lemmas become public; statements and bodies unchanged. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | A4 (new) | Reuses the original transport API. |
| Sheaf.Paper.CondensedLfpCoefficientModel | A4 | Reuses the original transport API. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Separate private `fp_extend`; unchanged. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| TargetsCheck | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Downstream importer; statements and definitions unchanged; no adaptation. |

`tools/downstream.py --uses` finds only the defining module for `fp_map` and
`fp_iff_of_iso`, and additionally IntegralReductionConstructible for the short
name `fp_extend` (that is a separate private helper). The two direct importers
above are the only direct importers of the adapted shared module. No downstream
statement changes, and no forced adaptation of another group's module is needed.

## Status

landed 20261016T073458-L-1079815 2026-10-16 (merge of deliver/A4/Sheaf.Paper.CondensedLfpCoefficientModel)
