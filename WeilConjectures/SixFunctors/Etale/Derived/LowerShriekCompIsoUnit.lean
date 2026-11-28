/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoAssoc
public import WeilConjectures.EtaleCohomology.Purity.Smooth.IdentitySquareBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import WeilConjectures.AlgebraicGeometry.ForgetSupportsComposition
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-!
# Unit laws of the composition isomorphism of the lower shriek

The composition isomorphisms `R(𝟙 ≫ b)_! ≅ R(𝟙)_! ⋙ Rb_!` and `R(a ≫ 𝟙)_! ≅ Ra_! ⋙ R(𝟙)_!`
of `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` are, through the identity isomorphism
`R(𝟙)_! ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`), the congruence
isomorphisms along `𝟙 ≫ b = b` and `a ≫ 𝟙 = a`. No finiteness assumption on the schemes is needed.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The composition isomorphism `R(𝟙)_* ⋙ R(𝟙)_* ≅ R(𝟙)_*` is the identity isomorphism
`R(𝟙)_* ≅ 𝟭` (`AlgebraicGeometry.Etale.rightDerivedLowerStarIdNatIso`). -/
lemma rightDerivedLowerStarCompIsoOfComp_id_hom_app (X : Scheme.{u})
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp _)).hom.app M =
      (rightDerivedLowerStarIdNatIso Λ X).hom.app
        ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj M) := by
  apply Adjunction.ext_of_comp_counit
    (adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
  have hc := leftDerivedUpperStarComp_id_left_hom_app (ModuleCat.{u + 1} Λ) (𝟙 X)
    ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj M))
  have hn := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit.app
      ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj M))
  have hn' := (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.naturality
    ((rightDerivedLowerStarIdNatIso Λ X).hom.app ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj M))
  simp only [Functor.id_map] at hn hn'
  rw [map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit,
    derivedUpperStarLowerStarAdjunction_id_counit_app (M := M), reassoc_of% hn, reassoc_of% hc,
    reassoc_of% hn', derivedUpperStarLowerStarAdjunction_id_counit_app,
    Category.assoc]

/-- For an endofunctor `F` with `e : F ≅ 𝟭`, the component of `e.inv` at `F.obj K` is `F` applied
to the component at `K`. -/
private lemma inv_app_obj_of_iso_id {C : Type*} [Category C] {F : C ⥤ C} (e : F ≅ 𝟭 C) (K : C) :
    e.inv.app (F.obj K) = F.map (e.inv.app K) :=
  (cancel_epi (e.inv.app K)).mp (e.inv.naturality (e.inv.app K))

/-- The congruence isomorphism `unboundedEtaleLowerShriekCongr` is the inverse of
`rightDerivedLowerShriekCongrIso` along the reversed equation. -/
private lemma unboundedEtaleLowerShriekCongr_eq_symm {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    unboundedEtaleLowerShriekCongr Λ h = (rightDerivedLowerShriekCongrIso Λ h.symm).symm := by
  subst h
  rfl

/-- For a proper `f`, the identification `Rf_! ≅ Rf_*` is the forget-supports map of the chosen
compactification of `f`. -/
lemma rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).hom =
      compactificationForgetSupports (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification f) := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq]
  rfl

variable [Finite Λ]

/-- The identifications `Rf_! ≅ Rf_*` of proper morphisms are compatible with the composition
isomorphisms of the lower shriek and of the lower star. -/
lemma rightDerivedLowerShriekCompIso_hom_app_comp_isoRightDerivedLowerStar {X Y Z : Scheme.{u}}
    (u₁ : X ⟶ Y) (u₂ : Y ⟶ Z) [IsProper u₁] [IsProper u₂] [IsProper (u₁ ≫ u₂)]
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCompIso Λ u₁ u₂).hom.app P ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₂).hom.app
          ((R(u₁)_![ModuleCat.{u + 1} Λ]).obj P) ≫
        (R((u₂)_*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₁).hom.app P) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ (u₁ ≫ u₂)).hom.app P ≫
        (rightDerivedLowerStarCompIsoOfComp _ u₁ u₂ (u₁ ≫ u₂) rfl).inv.app P := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom_eq_compactificationForgetSupports,
    ← cancel_mono ((rightDerivedLowerStarCompIsoOfComp _ u₁ u₂ (u₁ ≫ u₂) rfl).hom.app P)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← rightDerivedLowerShriekCompIso_inv_app_comp_forgetSupports, Iso.hom_inv_id_app_assoc]

/-- The identifications `Rf_! ≅ Rf_*` of proper morphisms are compatible with the composition
isomorphisms of the lower shriek and of the lower star, up to congruence along `u₁ ≫ u₂ = v`. -/
private lemma compIso_hom_app_comp_isoRightDerivedLowerStar {X Y Z : Scheme.{u}} (u₁ : X ⟶ Y)
    (u₂ : Y ⟶ Z) (v : X ⟶ Z) (h : u₁ ≫ u₂ = v) [IsProper u₁] [IsProper u₂] [IsProper v]
    [IsProper (u₁ ≫ u₂)]
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ h).inv.app P ≫
        (rightDerivedLowerShriekCompIso Λ u₁ u₂).hom.app P ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₂).hom.app
          ((R(u₁)_![ModuleCat.{u + 1} Λ]).obj P) ≫
        (R((u₂)_*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ u₁).hom.app P) =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar _ v).hom.app P ≫
        (rightDerivedLowerStarCompIsoOfComp _ u₁ u₂ v h).inv.app P := by
  subst h
  rw [rightDerivedLowerShriekCongrIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact rightDerivedLowerShriekCompIso_hom_app_comp_isoRightDerivedLowerStar Λ u₁ u₂ P

/-- The left unit law of `unboundedEtaleLowerShriekCompIso`, without finiteness assumptions. -/
private lemma unboundedEtaleLowerShriekCompIso_id_left_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [HasCompactification (𝟙 X ≫ f)]
    [QuasiCompact (𝟙 X ≫ f)] :
    (unboundedEtaleLowerShriekCompIso Λ (𝟙 X) f).hom =
      Functor.whiskerRight (unboundedEtaleLowerShriekId Λ X).hom _ ≫
        (Functor.leftUnitor _).hom ≫
        (unboundedEtaleLowerShriekCongr Λ (Category.id_comp f).symm).hom := by
  rw [← unbounded_chosen_comp Λ (𝟙 X) f, ← unbounded_chosen_id Λ X,
    ← unbounded_chosen_congr Λ (Category.id_comp f).symm]
  apply (config := { synthAssignedInstances := false })
    CompactSupportFormalism.lowerShriekCompIso_id_left

/-- The right unit law of `unboundedEtaleLowerShriekCompIso`, without finiteness assumptions. -/
private lemma unboundedEtaleLowerShriekCompIso_id_right_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [HasCompactification (f ≫ 𝟙 Y)]
    [QuasiCompact (f ≫ 𝟙 Y)] :
    (unboundedEtaleLowerShriekCompIso Λ f (𝟙 Y)).hom =
      Functor.whiskerLeft _ (unboundedEtaleLowerShriekId Λ Y).hom ≫
        (Functor.rightUnitor _).hom ≫
        (unboundedEtaleLowerShriekCongr Λ (Category.comp_id f).symm).hom := by
  rw [← unbounded_chosen_comp Λ f (𝟙 Y), ← unbounded_chosen_id Λ Y,
    ← unbounded_chosen_congr Λ (Category.comp_id f).symm]
  apply (config := { synthAssignedInstances := false })
    CompactSupportFormalism.lowerShriekCompIso_id_right

omit [Finite Λ] in
/-- The inverse of the composition isomorphism `R(𝟙)_* ⋙ R(𝟙)_* ≅ R(𝟙)_*`. -/
private lemma rightDerivedLowerStarCompIsoOfComp_id_inv_app (X : Scheme.{u})
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp _)).inv.app P =
      (rightDerivedLowerStarIdNatIso Λ X).inv.app ((R((𝟙 X)_*[ModuleCat.{u + 1} Λ])).obj P) := by
  rw [← cancel_epi ((rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} Λ) (𝟙 X) (𝟙 X) (𝟙 X)
    (Category.id_comp _)).hom.app P), Iso.hom_inv_id_app,
    rightDerivedLowerStarCompIsoOfComp_id_hom_app, Iso.hom_inv_id_app]
  rfl

/-- The composition isomorphism `R(𝟙 ≫ 𝟙)_! ≅ R(𝟙)_! ⋙ R(𝟙)_!`, up to congruence, is `R(𝟙)_!`
applied to the inverse of the identity isomorphism of the unbounded formalism. -/
private lemma congrIso_inv_app_comp_compIso_id_id_hom_app (X : Scheme.{u})
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ (Category.id_comp (𝟙 X))).inv.app P ≫
      (rightDerivedLowerShriekCompIso Λ (𝟙 X) (𝟙 X)).hom.app P =
      (R(𝟙 X)_![ModuleCat.{u + 1} Λ]).map ((unboundedEtaleLowerShriekId Λ X).inv.app P) := by
  rw [rightDerivedLowerShriekCompIso_eq_symm, Iso.symm_hom,
    ← cancel_mono ((unboundedEtaleLowerShriekCompIso Λ (𝟙 X) (𝟙 X)).hom.app P), Category.assoc,
    Iso.inv_hom_id_app, unboundedEtaleLowerShriekCompIso_id_left_hom, NatTrans.comp_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    unboundedEtaleLowerShriekCongr_eq_symm, Iso.symm_hom, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id ((rightDerivedLowerShriekCongrIso Λ (Category.id_comp (𝟙 X))).inv.app P),
    Category.id_comp ((rightDerivedLowerShriekCongrIso Λ (Category.id_comp (𝟙 X))).inv.app P)]
  exact (Category.id_comp _).symm

/-- In a category `C`, let `ι : F ≅ G`, `ρ : G ≅ 𝟭` and `ψ : F ≅ 𝟭` be isomorphisms of
endofunctors. If `F.map ψ⁻¹ ≫ ι ≫ G.map ι = ι ≫ ρ⁻¹` at `P`, then `ψ⁻¹ = ρ⁻¹ ≫ ι⁻¹` at `P`. -/
private lemma inv_app_eq_of_map_inv_app_comp {C : Type*} [Category C] {F G : C ⥤ C}
    (ι : F ≅ G) (ρ : G ≅ 𝟭 C) (ψ : F ≅ 𝟭 C) (P : C)
    (h : F.map (ψ.inv.app P) ≫ ι.hom.app (F.obj P) ≫ G.map (ι.hom.app P) =
      ι.hom.app P ≫ ρ.inv.app (G.obj P)) :
    ψ.inv.app P = ρ.inv.app P ≫ ι.inv.app P := by
  have : G.Faithful := Functor.Faithful.of_iso ρ.symm
  rw [reassoc_of% (ι.hom.naturality (ψ.inv.app P)), ← G.map_comp, cancel_epi,
    inv_app_obj_of_iso_id] at h
  rw [← G.map_injective h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The inverse of the identity isomorphism `R(𝟙)_! ≅ 𝟭` of the unbounded compact-support formalism
is the inverse of `R(𝟙)_! ≅ R(𝟙)_* ≅ 𝟭`. -/
private lemma unboundedEtaleLowerShriekId_inv_app (X : Scheme.{u})
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (unboundedEtaleLowerShriekId Λ X).inv.app P =
      (rightDerivedLowerStarIdNatIso Λ X).inv.app P ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
          (𝟙 X)).inv.app P := by
  have h := compIso_hom_app_comp_isoRightDerivedLowerStar Λ (𝟙 X) (𝟙 X) (𝟙 X)
    (Category.id_comp _) P
  rw [rightDerivedLowerStarCompIsoOfComp_id_inv_app,
    reassoc_of% congrIso_inv_app_comp_compIso_id_id_hom_app] at h
  exact inv_app_eq_of_map_inv_app_comp _ _ _ P h

/-- The identity isomorphism `R(𝟙)_! ≅ 𝟭` of the unbounded compact-support formalism is
`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`. -/
private lemma unboundedEtaleLowerShriekId_eq (X : Scheme.{u}) :
    unboundedEtaleLowerShriekId Λ X = rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X := by
  have hI : rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X =
      rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X) ≪≫
        rightDerivedLowerStarIdNatIso Λ X := rfl
  rw [hI]
  apply Iso.ext
  rw [← Iso.inv_eq_inv]
  ext P
  rw [unboundedEtaleLowerShriekId_inv_app, Iso.trans_inv, NatTrans.comp_app]

/-- **The left unit law** of the composition isomorphism of the lower shriek. -/
theorem rightDerivedLowerShriekCompIso_id_left_hom_app {X Y : Scheme.{u}} (b : X ⟶ Y)
    [HasCompactification b] [QuasiCompact b] [HasCompactification (𝟙 X ≫ b)]
    [QuasiCompact (𝟙 X ≫ b)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCompIso Λ (𝟙 X) b).hom.app K ≫
        (R(b)_![ModuleCat.{u + 1} Λ]).map
          ((rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom.app K) =
      (rightDerivedLowerShriekCongrIso Λ (Category.id_comp b)).hom.app K := by
  rw [← unboundedEtaleLowerShriekId_eq, rightDerivedLowerShriekCompIso_eq_symm, Iso.symm_hom,
    ← cancel_epi ((unboundedEtaleLowerShriekCompIso Λ (𝟙 X) b).hom.app K),
    Iso.hom_inv_id_app_assoc, unboundedEtaleLowerShriekCompIso_id_left_hom, NatTrans.comp_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    unboundedEtaleLowerShriekCongr_eq_symm, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.comp_id]

/-- **The right unit law** of the composition isomorphism of the lower shriek. -/
theorem rightDerivedLowerShriekCompIso_id_right_hom_app {X Y : Scheme.{u}} (a : X ⟶ Y)
    [HasCompactification a] [QuasiCompact a] [HasCompactification (a ≫ 𝟙 Y)]
    [QuasiCompact (a ≫ 𝟙 Y)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCompIso Λ a (𝟙 Y)).hom.app K ≫
        (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) Y).hom.app
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj K) =
      (rightDerivedLowerShriekCongrIso Λ (Category.comp_id a)).hom.app K := by
  rw [← unboundedEtaleLowerShriekId_eq, rightDerivedLowerShriekCompIso_eq_symm, Iso.symm_hom,
    ← cancel_epi ((unboundedEtaleLowerShriekCompIso Λ a (𝟙 Y)).hom.app K),
    Iso.hom_inv_id_app_assoc, unboundedEtaleLowerShriekCompIso_id_right_hom, NatTrans.comp_app,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    unboundedEtaleLowerShriekCongr_eq_symm, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Category.comp_id]

end AlgebraicGeometry.Etale
