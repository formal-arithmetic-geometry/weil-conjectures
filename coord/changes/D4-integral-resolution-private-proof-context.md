# AlgebraicGeometry.ProEtale.integral_lfp_locallyFree_resolution

## Reason

The static interface check classifies added `variable`, `open` and `attribute` commands
as an interface change. They elaborate private proved helpers for the pullback construction
and matrix-image induction. The attributes are explicitly `[local instance]`. No existing
public statement, definition, universe binder, visibility, public import, or target changes.
The only existing module edited is the D4 item. Four new modules and their nodes provide
the constructive free-generator API and the explicit local-to-global reduction.

## Old

```lean
theorem integral_lfp_locallyFree_resolution
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P) :
    ∃ (F₁ F₀ : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
      (f : F₁ ⟶ F₀) (g : F₀ ⟶ P) (w : f ≫ g = 0),
      (ShortComplex.mk f g w).ShortExact ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj F₁)) ∧
      (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj F₀)) := by
  sorry
```

No generic private-helper context or local preservation-instance attributes preceded
this theorem.

## New

The signature above is byte-identical; its proof is the concrete construction recorded
in the node and report. The added proof contexts are:

```lean
variable {C : Type u} [Category.{v} C] [Abelian C]
open CategoryTheory Limits
open scoped CategoryTheory.Obj ZeroObject
open MonoidalCategory MonObj
open Functor.LaxMonoidal Functor.OplaxMonoidal
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
```

The new generic declarations and all local-freeness glue in the existing module are
private and proved. They do not occur in any public signature. The proof-only imports
are ordinary `import`, including `import all` where an existing private API is reused.
The original public imports are unchanged. The local torsion-chart hole has its own
new module and node; the report identifies it as a decomposition with net zero holes.
All data definitions in the new generator module are actual composites of existing
functors, with the counit as the actual generator map.

## Users

`tools/downstream.py Sheaf.Paper.IntegralLfpLocallyFreeResolution --uses
integral_lfp_locallyFree_resolution` lists the following import closure. Only
`IntegralLfpHomContinuity` mentions the theorem outside the item. It compiled unchanged
against the delivered objects. The other listed modules have identical source statements
and definitions because no existing definition or public signature is changed.
Claim holders below are a read-only snapshot; none is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unchanged statement and definitions; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Existing signature and public imports unchanged; original consumer compiled without edits. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | D4 | Item: private proof helpers, proof imports, and file-local elaboration commands. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged statement and definitions; no adaptation. |
| TargetsCheck | unclaimed | Unchanged statement and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged statement and definitions; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged statement and definitions; no adaptation. |

No forced adaptations or target-definition changes are present.

## Status

landed 20261016T073459-L-1080136 2026-10-16 (merge of deliver/D4/Sheaf.Paper.IntegralLfpLocallyFreeResolution)
