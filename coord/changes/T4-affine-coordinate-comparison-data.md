# AlgebraicGeometry.AffineComparisonCoordinate, AffineComparisonKFlat, AffineCoordinateComparisonFamily

## Reason

Move the existing coordinate data into
`Sheaf.AlgebraicGeometry.AffineCoordinateComparisonData` so the proved helper modules can
state their interfaces without importing the theorem they prove. The original module
publicly imports this data module. Every declaration retains its name, universes,
binders, visibility and complete body verbatim. This changes neither the data nor the
meaning of any target; no statement review is reopened by a semantic change.

## Old

In `Sheaf.AlgebraicGeometry.AffineCoordinateComparisonCoherence`:

```lean
structure AffineComparisonCoordinate where
  A : CommRingCat.{u}
  X : Scheme.{u}
  σ : Spec A ≅ X
  d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X
  hd : DerivedCategory.Q ⋙ d.functor ≅
    (@Functor.mapHomologicalComplex ℤ
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
      (SheafOfModules.pushforward σ.hom.toRingCatSheafHom)
      ⟨fun _ _ ↦ rfl⟩ (.up ℤ)) ⋙ DerivedCategory.Q
  H : CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory X
  hH : H ≅
    (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) _ _ _ _
      (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
        (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙ d.functor

abbrev AffineComparisonKFlat (A : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
    (CochainComplex.mapBifunctor L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} A))).Acyclic

abbrev AffineCoordinateComparisonFamily : Type _ :=
  ∀ (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A) (p : b.X ⟶ a.X),
    b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom →
    ∀ (M N : CochainComplex (ModuleCat.{u} a.A) ℤ),
      AffineComparisonKFlat a.A M → AffineComparisonKFlat a.A N →
      (inducedFunctor (fun q : Bool ↦ cond q M N) ⋙
        (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ b.H ≅
      inducedFunctor (fun q : Bool ↦ cond q M N) ⋙ a.H ⋙ derivedPullback p)
```

## New

The same declarations, verbatim, in
`Sheaf.AlgebraicGeometry.AffineCoordinateComparisonData`:

```lean
structure AffineComparisonCoordinate where
  A : CommRingCat.{u}
  X : Scheme.{u}
  σ : Spec A ≅ X
  d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X
  hd : DerivedCategory.Q ⋙ d.functor ≅
    (@Functor.mapHomologicalComplex ℤ
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
      (SheafOfModules.pushforward σ.hom.toRingCatSheafHom)
      ⟨fun _ _ ↦ rfl⟩ (.up ℤ)) ⋙ DerivedCategory.Q
  H : CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory X
  hH : H ≅
    (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) _ _ _ _
      (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
        (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙ d.functor

abbrev AffineComparisonKFlat (A : CommRingCat.{u})
    (M : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  ∀ L : CochainComplex (ModuleCat.{u} A) ℤ, L.Acyclic →
    (CochainComplex.mapBifunctor L M
      (MonoidalCategory.curriedTensor (ModuleCat.{u} A))).Acyclic

abbrev AffineCoordinateComparisonFamily : Type _ :=
  ∀ (a b : AffineComparisonCoordinate.{u, w}) (φ : a.A →+* b.A) (p : b.X ⟶ a.X),
    b.σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ a.σ.hom →
    ∀ (M N : CochainComplex (ModuleCat.{u} a.A) ℤ),
      AffineComparisonKFlat a.A M → AffineComparisonKFlat a.A N →
      (inducedFunctor (fun q : Bool ↦ cond q M N) ⋙
        (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙ b.H ≅
      inducedFunctor (fun q : Bool ↦ cond q M N) ⋙ a.H ⋙ derivedPullback p)
```

The original module publicly re-exports them:

```lean
public import Sheaf.AlgebraicGeometry.AffineCoordinateComparisonData
```

## Users

The read-only `tools/downstream.py --uses` checks list the following existing users.
The coordinate and K-flat definitions are used by both rows; the family is used only
by the item module. No other existing module requires an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCoordinateComparisonCoherence | T4 | Imports the relocated data; statements unchanged; family theorem proved. |
| Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons | unclaimed in the local claim snapshot | Names, bodies and public visibility unchanged; original source requires no edit. |

The new modules of this delivery use these same definitions directly or through the
new concrete chart API. They impose no new condition on the original definitions.

## Status

landed 20261014T191827-L-824617 2026-10-14 (merge of deliver/T4/Sheaf.AlgebraicGeometry.AffineCoordinateComparisonCoherence)
