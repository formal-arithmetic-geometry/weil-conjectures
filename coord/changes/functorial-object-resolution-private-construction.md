# CochainComplex.exists_functorial_object_injective_resolution

## Reason

Complete the functorial objectwise injective resolution proof by explicit private constructions.
The interface checker reports added section commands (`noncomputable section`, `variable`,
local instance registrations), so this record documents their scope. The original public
signature, both public imports and all public declaration visibility are unchanged.

## Old

```lean
theorem exists_functorial_object_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A : C, Mono (η.app A)) (hJ : ∀ A : C, Injective (J.obj A)) :
    ∃ (E : C ⥤ CochainComplex C ℕ)
      (ε : (CochainComplex.single₀ C) ⟶ E),
      (∀ A : C, QuasiIso (ε.app A)) ∧
      (∀ (A B : C), E.map (0 : A ⟶ B) = 0) ∧
      IsZero (E.obj (0 : C)) ∧
      (∀ (A : C) (n : ℕ), Injective ((E.obj A).X n))
```

The whole proof was `by sorry`; no private constructions or section commands were present.

## New

```lean
theorem exists_functorial_object_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A : C, Mono (η.app A)) (hJ : ∀ A : C, Injective (J.obj A)) :
    ∃ (E : C ⥤ CochainComplex C ℕ)
      (ε : (CochainComplex.single₀ C) ⟶ E),
      (∀ A : C, QuasiIso (ε.app A)) ∧
      (∀ (A B : C), E.map (0 : A ⟶ B) = 0) ∧
      IsZero (E.obj (0 : C)) ∧
      (∀ (A : C) (n : ℕ), Injective ((E.obj A).X n))
```

The proof now builds the kernel normalization and iterated cokernel resolution, proves
naturality and exactness, and packages the four requested properties. Every new definition
and lemma is private. The five private zero-preservation instances are registered locally,
within the new noncomputable section, and have no downstream instance-search effect.
The section's category variables and all declaration-local options end in this file.
The only new import is the proof-only `Mathlib.Algebra.Homology.SingleHomology`.
No public definition changed, so no target meaning is reopened.

## Users

The source-only downstream inventory was checked with `tools/downstream.py`. The only direct
importer and caller is `Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution`.
Every downstream module below keeps the same statements and requires no adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same public signature and imports; no adaptation required. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same public signature and imports; no adaptation required. |
| TargetsCheck | unclaimed | Same public signature and imports; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same public signature and imports; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same public signature and imports; no adaptation required. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same public signature and imports; no adaptation required. |

## Status

landed 20261015T195758-L-1299825 2026-10-15 (merge of deliver/D4/Sheaf.Algebra.Homology.FunctorialObjectResolution)
