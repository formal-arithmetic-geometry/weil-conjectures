/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# The base change map for a pushforward tensored with the unit

For a commutative square `h ≫ f' = e ≫ g`, the base change map
`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)` of `AlgebraicGeometry.Etale.tensorBaseChangeMap`
at the unit `M = 𝟙_` is, up to the unitors and the monoidality of `Lh^*`, the derived base
change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` (`AlgebraicGeometry.Etale.derivedBaseChangeMap`).
In particular one is an isomorphism if and only if the other is
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_unit_iff`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.MonoidalCategory

/-- Whiskering on the left by an object isomorphic to the unit is, up to this isomorphism and
the left unitors, the identity. -/
lemma whiskerLeft_eq_leftUnitor_conj {C : Type*} [Category C] [MonoidalCategory C]
    {X Y Z : C} (ε : X ≅ 𝟙_ C) (c : Y ⟶ Z) :
    X ◁ c = ε.hom ▷ Y ≫ (λ_ Y).hom ≫ c ≫ (λ_ Z).inv ≫ ε.inv ▷ Z := by
  rw [leftUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc, ← whisker_exchange_assoc,
    ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.comp_id]

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

variable {X' S' T Y : Scheme.{u}}

omit [UpperStarPreservesFlat A] in
/-- The composite `Lh^* Lf'^* ⟶ L(h ≫ f')^* ≅ L(e ≫ g)^* ⟶ Le^* Lg^*` of composition
isomorphisms through a common diagonal `k` does not depend on the choice of `k`. -/
lemma leftDerivedUpperStarComp_inv_app_hom_app_eq (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
    (g : T ⟶ S') (k : Y ⟶ S') (p : k = h ≫ f') (q : k = e ≫ g)
    (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (leftDerivedUpperStarComp A h f' k p).inv.app K ≫
        (leftDerivedUpperStarComp A e g k q).hom.app K =
      (leftDerivedUpperStarComp A h f').inv.app K ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') (p.symm.trans q)).hom.app K := by
  subst p
  rfl

omit [UpperStarPreservesFlat A] in
/-- The derived square isomorphism `Lh^* Lf'^* ≅ Le^* Lg^*` of a square `h ≫ f' = e ≫ g`,
written through the diagonal `h ≫ f'`. -/
lemma derivedSquareUpperStarIso_hom_app_eq (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
    (g : T ⟶ S') (w : h ≫ f' = e ≫ g) (K : DerivedCategory (Sheaf S'.smallEtaleTopology A)) :
    (derivedSquareUpperStarIso A (CommSq.mk w.symm)).hom.app K =
      (leftDerivedUpperStarComp A h f').inv.app K ≫
        (leftDerivedUpperStarComp A e g (h ≫ f') w).hom.app K := by
  simp only [derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  exact leftDerivedUpperStarComp_inv_app_hom_app_eq A h e f' g _ _ _ K

/-- The base change map for a pushforward tensored with the unit `𝟙_` is, up to the left
unitors and the unit isomorphism `Lh^* 𝟙_ ≅ 𝟙_`, the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F`. -/
lemma tensorBaseChangeMap_unit_eq (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
    (g : T ⟶ S') (w : h ≫ f' = e ≫ g) (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMap A h e f' g w (𝟙_ _) F =
      (λ_ _).hom ≫ (derivedBaseChangeMap A (CommSq.mk w.symm)).app F ≫
        R((h)_*[A]).map ((λ_ _).inv ≫ (leftDerivedUpperStarUnitIso A h).inv ▷ _) := by
  apply ((derivedUpperStarLowerStarAdjunction A h).homEquiv _ _).symm.injective
  rw [tensorBaseChangeMap, Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
    derivedUpperStar_map_derivedBaseChangeMap_app_counit,
    derivedSquareUpperStarIso_hom_app_eq A h e f' g w,
    ← leftDerivedUpperStarTensorComparison_leftUnitor_hom]
  simp only [derivedTensor, curriedTensor_obj_map]
  rw [whiskerLeft_eq_leftUnitor_conj (leftDerivedUpperStarUnitIso A h)]
  simp only [Category.assoc]
  rfl

/-- The base change map for a pushforward tensored with the unit `𝟙_` is an isomorphism if and
only if the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F` is. -/
lemma isIso_tensorBaseChangeMap_unit_iff (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S')
    (g : T ⟶ S') (w : h ≫ f' = e ≫ g) (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    IsIso (tensorBaseChangeMap A h e f' g w (𝟙_ _) F) ↔
      IsIso ((derivedBaseChangeMap A (CommSq.mk w.symm)).app F) := by
  rw [tensorBaseChangeMap_unit_eq, isIso_comp_left_iff, isIso_comp_right_iff]

end Etale

end AlgebraicGeometry
