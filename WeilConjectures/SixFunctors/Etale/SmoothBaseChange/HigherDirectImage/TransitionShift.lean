/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctorPlus
public import WeilConjectures.CategoryTheory.Shift.AdjunctionHomEquiv
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition

/-!
# Shifted maps into a derived pushforward and the transition maps

For `h : Y ⟶ X`, `A ∈ D⁺(X_ét)` and `K ∈ D⁺(Y_ét)`, the adjunction `Lh^* ⊣ Rh_*` identifies
maps `A ⟶ (Rh_* K)⟦q⟧` with maps `h^* A ⟶ K⟦q⟧`
(`AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv`). Under this identification,
composition with the transition map `Rh_* K ⟶ Rh'_*(a^* K)` of a triangle `a ≫ h = h'`
(`AlgebraicGeometry.Etale.lowerStarPlusTransition`) becomes the pullback along `a`
(`AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv_comp_lowerStarPlusTransition`).

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv`:
  `(A ⟶ (Rh_* K)⟦q⟧) ≃ (h^* A ⟶ K⟦q⟧)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

instance Etale.commShift_upperStarPlusComp_hom {T S R : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) :
    NatTrans.CommShift (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) h₁ h₂).hom ℤ := by
  dsimp only [Etale.upperStarPlusComp, Iso.trans_hom]
  infer_instance

variable {X Y Y' : Scheme.{u}}

/-- The adjunction `Lh^* ⊣ Rh_*` on shifted maps: maps `A ⟶ (Rh_* K)⟦q⟧` correspond to maps
`h^* A ⟶ K⟦q⟧`, by applying `h^*` and the counit
(`AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv_apply`). -/
noncomputable def Etale.lowerStarPlusShiftedHomEquiv (h : Y ⟶ X) (q : ℤ)
    (A : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (A ⟶ (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)⟦q⟧) ≃
      (D+((h)^*[ModuleCat.{u + 1} Λ]).obj A ⟶ K⟦q⟧) :=
  (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).shiftedHomEquiv q A K

lemma Etale.lowerStarPlusShiftedHomEquiv_apply (h : Y ⟶ X) (q : ℤ)
    (A : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (x : A ⟶ (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)⟦q⟧) :
    Etale.lowerStarPlusShiftedHomEquiv Λ h q A K x =
      D+((h)^*[ModuleCat.{u + 1} Λ]).map x ≫
        (D+((h)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app
          K)⟦q⟧' :=
  Adjunction.shiftedHomEquiv_apply _ _ _ _ _

lemma Etale.lowerStarPlusShiftedHomEquiv_add (h : Y ⟶ X) (q : ℤ)
    (A : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (x y : A ⟶ (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)⟦q⟧) :
    Etale.lowerStarPlusShiftedHomEquiv Λ h q A K (x + y) =
      Etale.lowerStarPlusShiftedHomEquiv Λ h q A K x +
        Etale.lowerStarPlusShiftedHomEquiv Λ h q A K y := by
  simp only [Etale.lowerStarPlusShiftedHomEquiv_apply, Functor.map_add, Preadditive.add_comp]

lemma Etale.lowerStarPlusShiftedHomEquiv_zero (h : Y ⟶ X) (q : ℤ)
    (A : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.lowerStarPlusShiftedHomEquiv Λ h q A K 0 = 0 := by
  have e := Etale.lowerStarPlusShiftedHomEquiv_add Λ h q A K 0 0
  rw [add_zero] at e
  exact left_eq_add.mp e

/-- Under `AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv`, composition with the
transition map `Rh_* K ⟶ Rh'_*(a^* K)` of a triangle `a ≫ h = h'` is the pullback along `a`:
`h'^* A ≅ a^* h^* A ⟶ a^*(K⟦q⟧) ≅ (a^* K)⟦q⟧`. -/
lemma Etale.lowerStarPlusShiftedHomEquiv_comp_lowerStarPlusTransition (a : Y' ⟶ Y)
    (h : Y ⟶ X) (h' : Y' ⟶ X) (w : a ≫ h = h') (q : ℤ)
    (A : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (x : A ⟶ (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)⟦q⟧) :
    Etale.lowerStarPlusShiftedHomEquiv Λ h' q A _
        (x ≫ (Etale.lowerStarPlusTransition Λ a h h' w K)⟦q⟧') =
      (eqToIso (by rw [← w]) ≪≫ Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h).hom.app A ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map (Etale.lowerStarPlusShiftedHomEquiv Λ h q A K x) ≫
        (D+((a)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app K := by
  subst w
  simp only [eqToIso_refl, Iso.refl_trans]
  set c := Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a h
  set adj := Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h
  set adj' := Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (a ≫ h)
  have key : D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map
        (Etale.lowerStarPlusTransition Λ a h (a ≫ h) rfl K) ≫
      adj'.counit.app (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K) =
      c.hom.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K) ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map (adj.counit.app K) := by
    dsimp only [Etale.lowerStarPlusTransition]
    rw [eqToIso_refl, Iso.refl_trans, ← Adjunction.homEquiv_unit]
    exact (Adjunction.homEquiv_counit _ _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  have key' : D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.lowerStarPlusTransition Λ a h (a ≫ h) rfl K)⟦q⟧') ≫
      (D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
      (adj'.counit.app (D+((a)^*[ModuleCat.{u + 1} Λ]).obj K))⟦q⟧' =
      (D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
        (c.hom.app (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K))⟦q⟧' ≫
        (D+((a)^*[ModuleCat.{u + 1} Λ]).map (adj.counit.app K))⟦q⟧' := by
    rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, key, Functor.map_comp]
  have nat : c.hom.app A ≫ D+((a)^*[ModuleCat.{u + 1} Λ]).map
        (D+((h)^*[ModuleCat.{u + 1} Λ]).map x) =
      D+((a ≫ h)^*[ModuleCat.{u + 1} Λ]).map x ≫ c.hom.app _ :=
    (c.hom.naturality x).symm
  have hc := NatTrans.shift_app_comm c.hom q (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)
  rw [Functor.commShiftIso_comp_hom_app] at hc
  have na := (D+((a)^*[ModuleCat.{u + 1} Λ])).commShiftIso_hom_naturality
    ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app K) q
  rw [Etale.lowerStarPlusShiftedHomEquiv_apply, Etale.lowerStarPlusShiftedHomEquiv_apply,
    Functor.map_comp, Category.assoc, key', reassoc_of% hc, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc]
  erw [na]
  rw [reassoc_of% nat]
  rfl

/-- Naturality of `AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv` in `K`. -/
lemma Etale.lowerStarPlusShiftedHomEquiv_comp_map (h : Y ⟶ X) (q : ℤ)
    (A : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {K K' : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (x : A ⟶ (R+((h)_*[ModuleCat.{u + 1} Λ]).obj K)⟦q⟧) (f : K ⟶ K') :
    Etale.lowerStarPlusShiftedHomEquiv Λ h q A K'
        (x ≫ (R+((h)_*[ModuleCat.{u + 1} Λ]).map f)⟦q⟧') =
      Etale.lowerStarPlusShiftedHomEquiv Λ h q A K x ≫ f⟦q⟧' := by
  rw [Etale.lowerStarPlusShiftedHomEquiv_apply, Etale.lowerStarPlusShiftedHomEquiv_apply,
    Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality_assoc,
    Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 3
  exact (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit_naturality f

end AlgebraicGeometry
