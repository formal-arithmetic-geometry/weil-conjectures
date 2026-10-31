/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! Computing the derived image of a single object with a specified resolution.
Source: Stacks Project, Tags 0118, 0156 and 015X.
(blueprint: lem-sp-specified-resolution-derived-single).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

/-- The image of the specified injective resolution, with its lower bound. -/
noncomputable def specifiedResolutionComplex {X : C} (R : InjectiveResolution X) :
    CochainComplex.Plus D :=
  ⟨(F.mapHomologicalComplex _).obj R.cochainComplex, 0, inferInstance⟩

/-- The derived image of a single object is computed by any specified injective resolution.
Source: Stacks Project, Tag 0156; the normalization is the mapped augmentation followed
by the inverse derived unit (blueprint: lem-sp-specified-resolution-derived-single). -/
noncomputable def specifiedResolutionDerivedSingleIso {X : C} (R : InjectiveResolution X) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≅
      DerivedCategory.Plus.Q.obj (F.specifiedResolutionComplex R) :=
  let L : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  have : ∀ n, Injective (L.obj.X n) := fun n ↦ inferInstanceAs (Injective (R.cochainComplex.X n))
  F.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
      asIso (DerivedCategory.Q.map R.ι') ≪≫ (DerivedCategory.quotientCompQhIso C).symm.app _)) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L))).symm

/-- Specified-resolution comparisons commute with maps lifting maps of the resolved objects.
Source: Stacks Project, Tag 0156
(blueprint: lem-sp-specified-resolution-derived-single).

Proof. The augmentation square gives a square after localization, including the canonical
single-complex and quotient comparisons. Apply the derived functor, and commute the inverse
derived units using naturality of the unit. -/
@[reassoc]
theorem specifiedResolutionDerivedSingleIso_naturality {X Y : C} {f : X ⟶ Y}
    (R : InjectiveResolution X) (R' : InjectiveResolution Y) (φ : R.Hom R' f) :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map f) ≫
        (F.specifiedResolutionDerivedSingleIso R').hom =
      (F.specifiedResolutionDerivedSingleIso R).hom ≫
        DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          ((F.mapHomologicalComplex _).map φ.hom') :
            F.specifiedResolutionComplex R ⟶ F.specifiedResolutionComplex R') := by
  let LX : CochainComplex.Plus C := ⟨R.cochainComplex, 0, inferInstance⟩
  let LY : CochainComplex.Plus C := ⟨R'.cochainComplex, 0, inferInstance⟩
  let g : LX ⟶ LY := ObjectProperty.homMk φ.hom'
  have h₁ := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient C).map g)
  have h₂ : (DerivedCategory.Plus.singleFunctor C 0).map f ≫
      (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor C 0).obj Y)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj LY))
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app Y ≪≫
          asIso (DerivedCategory.Q.map R'.ι') ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).hom =
      (DerivedCategory.Plus.ι.preimageIso (X := (DerivedCategory.Plus.singleFunctor C 0).obj X)
        (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj LX))
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫
          asIso (DerivedCategory.Q.map R.ι') ≪≫
          (DerivedCategory.quotientCompQhIso C).symm.app _)).hom ≫
        DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    have := (DerivedCategory.quotientCompQhIso C).inv.naturality φ.hom'
    simp only [CategoryTheory.Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
    dsimp at this ⊢
    change (DerivedCategory.singleFunctor C 0).map f ≫ _ =
      _ ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C _).map φ.hom')
    rw [Category.assoc, Category.assoc, ← this,
      (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality_assoc]
    simp only [Functor.comp_map, ← CategoryTheory.Functor.map_comp_assoc,
      InjectiveResolution.Hom.ι'_comp_hom']
  dsimp [specifiedResolutionDerivedSingleIso]
  rw [← F.rightDerivedFunctorPlus.map_comp_assoc, h₂, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact h₁.symm

end CategoryTheory.Functor
