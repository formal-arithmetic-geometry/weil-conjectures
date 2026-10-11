/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Coherence of the composition isomorphisms of total right derived functors

For additive functors preserving K-injective complexes, the composition isomorphisms
`Functor.rightDerivedFunctorCompIso' : RF ⋙ RG ≅ RH` attached to isomorphisms `F ⋙ G ≅ H` are
natural and satisfy the cocycle condition: for `F₁ ⋙ F₂ ≅ F₁₂`, `F₂ ⋙ F₃ ≅ F₂₃`,
`F₁₂ ⋙ F₃ ≅ F₁₃` and `F₁ ⋙ F₂₃ ≅ F₁₃` satisfying the cocycle condition, the two composite
isomorphisms `RF₁ ⋙ RF₂ ⋙ RF₃ ≅ RF₁₃` agree
(`CategoryTheory.Functor.rightDerivedFunctorCompIso'_cocycle`). This makes the right derived
functors of a pseudofunctor into additive categories a pseudofunctor, as needed for the
transition functors of the `ℚ̄_ℓ` coefficient stage.

All statements are proved through the universal property of the right derived functor
(`CategoryTheory.Functor.rightDerived_ext`), by comparing the composites with the units.
-/

@[expose] public section

set_option linter.unusedSectionVars false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory Category Limits Abelian

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₂] [HasKInjectiveResolutions C₃]
  [HasKInjectiveResolutions C₄]

section NatTrans

variable {F G H : C₁ ⥤ C₂} [F.Additive] [G.Additive] [H.Additive]

@[reassoc (attr := simp)]
lemma rightDerivedFunctorNatTrans_fac_app (τ : F ⟶ G) (X : HomotopyCategory C₁ (.up ℤ)) :
    F.rightDerivedFunctorUnit.app X ≫ (rightDerivedFunctorNatTrans τ).app
      (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app X) ≫
        G.rightDerivedFunctorUnit.app X := by
  simp [rightDerivedFunctorNatTrans]

@[simp]
lemma rightDerivedFunctorNatTrans_comp (τ : F ⟶ G) (τ' : G ⟶ H) :
    rightDerivedFunctorNatTrans τ ≫ rightDerivedFunctorNatTrans τ' =
      rightDerivedFunctorNatTrans (τ ≫ τ') := by
  simp [rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp]

end NatTrans

section Comp

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive] [G.Additive]

lemma rightDerivedFunctorCompUnit_app (X : HomotopyCategory C₁ (.up ℤ)) :
    (rightDerivedFunctorCompUnit F G).app X =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have h : (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app X = 𝟙 _ := by
    rw [← cancel_mono ((mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app X),
      Iso.inv_hom_id_app, mapHomotopyCategoryCompIso_refl_hom_app, id_comp]
    rfl
  simp [rightDerivedFunctorCompUnit, h]

@[reassoc (attr := simp)]
lemma rightDerivedFunctorCompIso_hom_fac_app [F.PreservesKInjectiveComplexes]
    (X : HomotopyCategory C₁ (.up ℤ)) :
    (F ⋙ G).rightDerivedFunctorUnit.app X ≫
        (rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj X) =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  rw [← rightDerivedFunctorCompUnit_app]
  simp [rightDerivedFunctorCompIso]

/-- Naturality of the composition isomorphism in the first functor. -/
lemma rightDerivedFunctorCompIso_hom_naturality_left {F' : C₁ ⥤ C₂} [F'.Additive]
    [F.PreservesKInjectiveComplexes] [F'.PreservesKInjectiveComplexes] (τ : F ⟶ F') :
    (rightDerivedFunctorCompIso F G).hom ≫
        Functor.whiskerRight (rightDerivedFunctorNatTrans τ) G.rightDerivedFunctor =
      rightDerivedFunctorNatTrans (Functor.whiskerRight τ G) ≫
        (rightDerivedFunctorCompIso F' G).hom := by
  refine rightDerived_ext _ (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) _ _ _ (NatTrans.ext (funext fun X ↦ ?_))
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightDerivedFunctorCompIso_hom_fac_app_assoc, rightDerivedFunctorNatTrans_fac_app_assoc,
    ← Functor.map_comp]
  rw [rightDerivedFunctorNatTrans_fac_app, Functor.map_comp]
  have := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory τ (.up ℤ)).app ((HomotopyCategory.quotient _ _).obj K))
  dsimp at this
  rw [← reassoc_of% this, rightDerivedFunctorCompIso_hom_fac_app]
  rfl

/-- Naturality of the composition isomorphism in the second functor. -/
lemma rightDerivedFunctorCompIso_hom_naturality_right {G' : C₂ ⥤ C₃} [G'.Additive]
    [F.PreservesKInjectiveComplexes] (σ : G ⟶ G') :
    (rightDerivedFunctorCompIso F G).hom ≫
        Functor.whiskerLeft F.rightDerivedFunctor (rightDerivedFunctorNatTrans σ) =
      rightDerivedFunctorNatTrans (Functor.whiskerLeft F σ) ≫
        (rightDerivedFunctorCompIso F G').hom := by
  refine rightDerived_ext _ (F ⋙ G).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) _ _ _ (NatTrans.ext (funext fun X ↦ ?_))
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    rightDerivedFunctorCompIso_hom_fac_app_assoc, rightDerivedFunctorNatTrans_fac_app_assoc,
]
  erw [(rightDerivedFunctorNatTrans σ).naturality]
  rw [reassoc_of% (rightDerivedFunctorNatTrans_fac_app σ _),
    rightDerivedFunctorCompIso_hom_fac_app]
  rfl

end Comp

section Assoc

variable (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃) (F₃ : C₃ ⥤ C₄) [F₁.Additive] [F₂.Additive] [F₃.Additive]
  [F₁.PreservesKInjectiveComplexes] [F₂.PreservesKInjectiveComplexes]

/-- Associativity of the composition isomorphisms of right derived functors. -/
lemma rightDerivedFunctorCompIso_assoc :
    (rightDerivedFunctorCompIso (F₁ ⋙ F₂) F₃).hom ≫
        Functor.whiskerRight (rightDerivedFunctorCompIso F₁ F₂).hom F₃.rightDerivedFunctor =
      (rightDerivedFunctorCompIso F₁ (F₂ ⋙ F₃)).hom ≫
        Functor.whiskerLeft F₁.rightDerivedFunctor (rightDerivedFunctorCompIso F₂ F₃).hom := by
  refine rightDerived_ext _ ((F₁ ⋙ F₂) ⋙ F₃).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) _ _ _ (NatTrans.ext (funext fun X ↦ ?_))
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [rightDerivedFunctorCompIso_hom_fac_app_assoc (F₁ ⋙ F₂) F₃, ← Functor.map_comp,
    rightDerivedFunctorCompIso_hom_fac_app]
  erw [rightDerivedFunctorCompIso_hom_fac_app_assoc F₁ (F₂ ⋙ F₃)]
  erw [(rightDerivedFunctorCompIso F₂ F₃).hom.naturality]
  erw [rightDerivedFunctorCompIso_hom_fac_app_assoc F₂ F₃]
  simp only [Functor.comp_map, Functor.map_comp]
  rfl

variable {F₁ F₂ F₃} {F₁₂ : C₁ ⥤ C₃} {F₂₃ : C₂ ⥤ C₄} {F₁₃ : C₁ ⥤ C₄} [F₁₂.Additive] [F₂₃.Additive]
  [F₁₃.Additive] [F₁₂.PreservesKInjectiveComplexes]

/-- **The cocycle condition for the composition isomorphisms of right derived functors.** If the
isomorphisms `e₁₂ : F₁ ⋙ F₂ ≅ F₁₂`, `e₂₃ : F₂ ⋙ F₃ ≅ F₂₃`, `e : F₁₂ ⋙ F₃ ≅ F₁₃` and
`e' : F₁ ⋙ F₂₃ ≅ F₁₃` satisfy the cocycle condition, so do the induced isomorphisms of right
derived functors. -/
theorem rightDerivedFunctorCompIso'_cocycle (e₁₂ : F₁ ⋙ F₂ ≅ F₁₂) (e₂₃ : F₂ ⋙ F₃ ≅ F₂₃)
    (e : F₁₂ ⋙ F₃ ≅ F₁₃) (e' : F₁ ⋙ F₂₃ ≅ F₁₃)
    (h : Functor.whiskerRight e₁₂.hom F₃ ≫ e.hom = Functor.whiskerLeft F₁ e₂₃.hom ≫ e'.hom) :
    Functor.whiskerRight (rightDerivedFunctorCompIso' F₁ F₂ e₁₂).hom F₃.rightDerivedFunctor ≫
        (rightDerivedFunctorCompIso' F₁₂ F₃ e).hom =
      Functor.whiskerLeft F₁.rightDerivedFunctor (rightDerivedFunctorCompIso' F₂ F₃ e₂₃).hom ≫
        (rightDerivedFunctorCompIso' F₁ F₂₃ e').hom := by
  rw [← cancel_epi ((rightDerivedFunctorCompIso (F₁ ⋙ F₂) F₃).hom ≫
    Functor.whiskerRight (rightDerivedFunctorCompIso F₁ F₂).hom F₃.rightDerivedFunctor)]
  conv_rhs => rw [rightDerivedFunctorCompIso_assoc]
  simp only [rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom, Category.assoc,
    rightDerivedFunctorNatIso,
    Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
  simp only [← Category.assoc, ← Functor.whiskerRight_comp, ← Functor.whiskerLeft_comp,
    Iso.hom_inv_id, Category.id_comp]
  simp only [Category.assoc]
  rw [reassoc_of% rightDerivedFunctorCompIso_hom_naturality_left,
    reassoc_of% rightDerivedFunctorCompIso_hom_naturality_right]
  simp only [Iso.hom_inv_id_assoc, rightDerivedFunctorNatTrans_comp]
  rw [h]

end Assoc

end CategoryTheory.Functor
