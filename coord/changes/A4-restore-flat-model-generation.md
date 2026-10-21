# AlgebraicGeometry.FlatModelOrderedStratification

## Reason

Restore the missing rework item from
`quarantine/Sheaf/SixFunctors/FlatModelGeneration.lean`, as recorded in
`coord/rework.tsv`. The archive failed lcompile.py with
`Unknown identifier LocallyClosedStratification` in six places. The retirement record
`retire-sheaf-twins-20261020.md` records the migration to `Scheme.Stratification`.
The current upstream `WeilConjectures.ConstructibleSheaf.Defs` supplies that structure.

Replace only the six obsolete type-name occurrences (five public signatures and one
private helper signature). All definitions, theorem bodies, declarations, visibility,
imports, docstrings and dependencies are otherwise preserved from the archive. The
ordered predicate still asserts exactly closed tails and relative openness.

The current structure additionally records constructibility of the strata. On every
Noetherian scheme of this node, any locally closed subset is constructible by
`IsLocallyClosed.isConstructible_of_noetherianSpace`. Thus the same finite partitions,
scheme structures and immersion maps remain available; no mathematical hypothesis or
conclusion changes. No positivity condition is added: an empty scheme can still use
zero strata, and the existing proofs handle that case. The existing
`Stratification.ofNoetherianSpace` construction supplies the constructibility field.
Neither coefficient universes nor arbitrary nonreduced stratum structures change.

This is a restoration/API repair, not a new proof of the pro-etale clauses. All three
original named pro-etale holes remain in place. The source library is untouched.

## Old

The active module is absent. The affected public signatures in the archive are:

```lean
def FlatModelOrderedStratification {X : Scheme.{u}} (str : LocallyClosedStratification X) :
    Prop

theorem etale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F) (_hf : ObjectProperty.flat F) :
    ∃ str : LocallyClosedStratification X,
      FlatModelOrderedStratification str ∧
      ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
        ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)

theorem proEtale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F)
    (_hf : SheafOfModules.IsFlatOnSite (J

theorem etale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F)
    (_hf : ObjectProperty.flat F)
    (str : LocallyClosedStratification X) (_ho : FlatModelOrderedStratification str)
    (_hp : ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
      ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) :
    FlatModelExtensionFiltration
      (fun k : Fin str.n ↦
        (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) F ∧
    ∀ k : Fin str.n,
      ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        G = (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F) ∧
        ObjectProperty.flat G ∧
        IsConstructibleEtaleModuleSheaf G ∧
        (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G))

theorem proEtale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F)
    (_hf : SheafOfModules.IsFlatOnSite (J
```

## New

Restore the archived module with these current signatures:

```lean
def FlatModelOrderedStratification {X : Scheme.{u}} (str : Stratification X) :
    Prop

theorem etale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F) (_hf : ObjectProperty.flat F) :
    ∃ str : Stratification X,
      FlatModelOrderedStratification str ∧
      ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
        ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)

theorem proEtale_flatConstructible_orderedStratification
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F)
    (_hf : SheafOfModules.IsFlatOnSite (J

theorem etale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hc : IsConstructibleEtaleModuleSheaf F)
    (_hf : ObjectProperty.flat F)
    (str : Stratification X) (_ho : FlatModelOrderedStratification str)
    (_hp : ∀ k : Fin str.n, FlatModelEtaleLisseProjective A
      ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) :
    FlatModelExtensionFiltration
      (fun k : Fin str.n ↦
        (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F)) F ∧
    ∀ k : Fin str.n,
      ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        G = (flatModelEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) (str.immersion k)).obj F) ∧
        ObjectProperty.flat G ∧
        IsConstructibleEtaleModuleSheaf G ∧
        (∀ q : ℤ, IsConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj G))) ∧
        (∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G))

theorem proEtale_flatConstructible_extensionFiltration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A))
    (_hc : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F)
    (_hf : SheafOfModules.IsFlatOnSite (J
```

The private `flatModel_etale_ordered_filtration` signature has the same type-name
replacement. The node's Lean signature and note are refreshed; its attachment,
mathematical statement, proof, dependencies and unit route stay unchanged.

## Users

`tools/downstream.py Sheaf.SixFunctors.FlatModelGeneration --uses
FlatModelOrderedStratification` reports `unknown module(s)` because the active item
is absent. A search of every live Lean source finds no references to this module or
its declarations. A separate search of the quarantine archives finds these four
importers; they remain quarantined and are not modified by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FlatModelGeneration | A4 | Restore and migrate six obsolete type names. |
| Sheaf.SixFunctors.FlatModel | unclaimed in local claim records | Archived consumer; uses the three etale theorems with an inferred stratum variable. The calls at lines 480, 482 and 738 accept the current Stratification without adaptation. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed in local claim records | Archived import only; no occurrence of the migrated signatures or predicate. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed in local claim records | Archived import only; no occurrence of the migrated signatures or predicate. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed in local claim records | Archived import only; no occurrence of the migrated signatures or predicate. |

No consumer declaration changes, no deletion, no withdrawal, and no forced adaptation.
This preserves the statements used along the target route; Challenge.lean is untouched.

## Status

landed 20261021T012346-L-2179442 2026-10-21 (merge of deliver/A4/Sheaf.SixFunctors.FlatModelGeneration)
