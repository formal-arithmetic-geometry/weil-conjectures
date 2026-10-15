# CochainComplex.exists_isKFlatResolutionGeneral

## Reason

Prove the independent-site-universe theorem from the generic source resolution.
The preflight regards newly added `open`, `variable`, local notation, and local
instance attributes as an interface change. This record documents those proof
elaboration commands and the private helpers they support. All original public
imports are retained, the sole original public declaration has exactly the same
signature, and every newly declared helper is private. The local instance
attributes and local notations do not export an instance or notation to importers.
There is no changed target statement, public definition, or public instance.
No other Lean module is changed or needs adaptation.

## Old

```lean
theorem exists_isKFlatResolutionGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    (G : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
      (f : K ⟶ G), CochainComplex.IsKFlat K ∧
        (∀ i : ℤ, exactFunctor _ _
          (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (K.X i))) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  sorry
```

The module had `open CategoryTheory` and no proof-local helper sections.

## New

```lean
theorem exists_isKFlatResolutionGeneral
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{max u v}}
    (G : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ) :
    ∃ (K : CochainComplex (SheafOfModules.{max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ℤ)
      (f : K ⟶ G), CochainComplex.IsKFlat K ∧
        (∀ i : ℤ, exactFunctor _ _
          (@MonoidalCategory.tensorRight _ _ (SheafOfModules.monoidalCategory R) (K.X i))) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i))
```

The signature above is unchanged verbatim. Its complete proof now uses private
helpers in the `PresheafOfModules`, `SheafOfModules`, and `CochainComplex`
namespaces. The file additionally opens `MonoidalCategory`, `Limits`, `Opposite`,
and the `ZeroObject` scope, and uses namespace-local variables, notation, and
local instance attributes to elaborate those helpers. No public definition or
signature incorporates a private helper. The theorem proof is the only public
body that invokes them.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.KFlatResolutionGeneral --uses
CochainComplex.exists_isKFlatResolutionGeneral` reports 25 downstream importers
and no downstream occurrence of the theorem name. Every importer is listed
below for completeness. Holders are the snapshot recorded in this checkout;
none of their modules is modified. Since public imports and signatures are
unchanged, none requires a forced adaptation or a statement review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatResolutionGeneral | B2 | Proof completed; signature unchanged. |
| Sheaf.Algebra.Homology.DerivedChangeOfRingsGeneral | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No edits; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOperations | C3 | No edits; public signature and imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.CompleteCoefficientDatum | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | No edits; public signature and imports unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.ProEtaleConstructibleSheaf | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | No edits; public signature and imports unchanged. |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | No edits; public signature and imports unchanged. |
| TargetsCheck | unclaimed | No edits; public signature and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No edits; public signature and imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | C1 | No edits; public signature and imports unchanged. |

## Status

landed 20261015T154150-L-158307 2026-10-15 (merge of deliver/B2/Sheaf.Algebra.Homology.KFlatResolutionGeneral)
