# CategoryTheory.Functor.residueDerivedMonoidal

## Reason

Repeated specialization of the complete CoreMonoidal coherence structure exceeded the
single-file compilation limit. Keep the construction body exactly as before, cache it with
`no_expose, irreducible`, and expose a proved tensor-component equation. This changes elaboration
transparency only; the underlying monoidal structure and all existing signatures are identical.
The module is unclaimed. Definitions occurring in targets retain precisely the same bodies;
the independent reader should check this definitional identity when reviewing the target API.

## Old

```lean
@[instance_reducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  letI := residueDerivedOplax F
  haveI := residueDerivedOplax_isIso_δ F
  haveI := residueDerivedOplax_isIso_η F
  exact (CoreMonoidal.ofOplaxMonoidal _).toMonoidal
```

The original typed wrapper was:

```lean
@[instance_reducible] noncomputable def residueExchangePullMonoidal
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal := by
  letI := m
  letI := hFlat
  unfold residueExchangeUpperStar
  exact (f)^*⟦integralCoeff ℓ E⟧.residueDerivedMonoidal
```

## New

```lean
@[no_expose, irreducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  letI := residueDerivedOplax F
  haveI := residueDerivedOplax_isIso_δ F
  haveI := residueDerivedOplax_isIso_η F
  exact (CoreMonoidal.ofOplaxMonoidal _).toMonoidal


/-- The tensor component of the cached derived monoidal structure is the canonical
left-derived tensor comparison. -/
theorem residueDerivedMonoidal_δ (M N : DerivedCategory C) :
    letI := residueDerivedMonoidal F
    OplaxMonoidal.δ F.leftDerivedFunctor M N =
      (F.leftDerivedTensorComparison.app M).app N := by
  unfold residueDerivedMonoidal
  rfl
```

The typed wrapper is cached too, with its unchanged body and a proved defining equation:

```lean
@[no_expose, irreducible] noncomputable def residueExchangePullMonoidal
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal := by
  letI := m
  letI := hFlat
  unfold residueExchangeUpperStar
  exact (f)^*⟦integralCoeff ℓ E⟧.residueDerivedMonoidal


/-- The cached pullback structure is the canonical generic derived structure.
Source: the defining derived monoidal construction.
(blueprint: new-integral-residue-derived-monoidal)
Proof. Unfold the typed pullback wrapper; the two constructions are identical. -/
theorem residueExchangePullMonoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat) :
    letI := m
    letI := hFlat
    residueExchangePullMonoidal ℓ E f m hFlat =
      (by
        unfold residueExchangeUpperStar
        exact Functor.residueDerivedMonoidal (f)^*⟦integralCoeff ℓ E⟧) := by
  unfold residueExchangePullMonoidal
  rfl
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Unchanged construction body; non-exposure, opacity and a proved tensor-component API added. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | A4 | Uses the component API instead of expanding the coherence structure. |

`tools/downstream.py Sheaf.Paper.IntegralResidueDerivedMonoidal --uses residueDerivedMonoidal`
finds only the defining module as a textual user, and 37 transitive importers, listed below. The public
scheme-level wrapper is unchanged and reexports the same constructed structure. Existing
consumer statements are neither strengthened nor weakened. No consumer adaptation is required.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueOrdinaryTensorNormalization | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | claimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Unchanged statements, data and imports; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged statements, data and imports; no adaptation. |
| TargetsCheck | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged statements, data and imports; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged statements, data and imports; no adaptation. |

## Status

landed 20261017T144415-L-4152973 2026-10-17 (merge of deliver/A4/Sheaf.Paper.IntegralResidueTensorRouteModel)
