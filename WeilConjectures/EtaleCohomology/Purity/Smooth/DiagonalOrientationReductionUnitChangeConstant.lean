/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.MonoidalUnit
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalSheaf
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClassCoefficientChange

/-!
# The change of coefficients of the constant sheaf `ℤ` is the unit map

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings. The change of coefficients
`Λ ⊗ ℤ ⟶ Res(Λ' ⊗ ℤ)` of the constant étale sheaf `ℤ`
(`AlgebraicGeometry.Etale.extendScalarsChangeMap`) is, through the identifications
`Λ ⊗ ℤ ≅ Λ_X` and `Λ' ⊗ ℤ ≅ Λ'_X`, the unit map `Λ_X ⟶ Res Λ'_X` of the extension of scalars
along `ρ`, the adjoint of its unit comparison
(`AlgebraicGeometry.Etale.extendScalarsConstantZModIso_inv_comp_changeMap_app_comp`).

Both maps are compared through their adjoints `ℤ ⟶ Γ(X, Res Λ'_X)`, which send `1` to `1`. For
the unit map this uses that the adjoint of the unit `ε : 𝟙 ⟶ G_* 𝟙` of the postcomposition of
sheaves with a lax monoidal functor `G` under the constant sheaf adjunction is `ε G` followed by
`G` of the unit (`CategoryTheory.constantSheafAdj_homEquiv_ε_sheafCompose`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

open Functor.LaxMonoidal

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A]
  {B : Type*} [Category B] [MonoidalCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G] [G.LaxMonoidal]

attribute [local instance] Sheaf.monoidalCategory

/-- The adjoint under the constant sheaf adjunction of the unit `ε : 𝟙 ⟶ G_* 𝟙` of the
postcomposition of sheaves with a lax monoidal functor `G` is `ε G : 𝟙 ⟶ G 𝟙` followed by `G` of
the unit `𝟙 ⟶ Γ(𝟙)` of the constant sheaf adjunction. -/
lemma constantSheafAdj_homEquiv_ε_sheafCompose {T : C} (hT : IsTerminal T) :
    (constantSheafAdj J B hT).homEquiv (𝟙_ B) ((sheafCompose J G).obj (𝟙_ (Sheaf J A)))
        (ε (sheafCompose J G)) =
      ε G ≫ G.map ((constantSheafAdj J A hT).unit.app (𝟙_ A)) := by
  rw [Adjunction.homEquiv_unit, constantSheafAdj, Adjunction.comp_unit_app]
  erw [Adjunction.comp_unit_app]
  have h := ε_sheafToPresheaf_app_comp_ε_sheafCompose_app J G (Opposite.op T)
  rw [ε_sheafToPresheaf_eq_toSheafify, ε_sheafToPresheaf_eq_toSheafify] at h
  simp only [sheafificationAdjunction_unit_app, constantPresheafAdj,
    Functor.constCompEvaluationObj, evaluation_obj_map, NatIso.ofComponents_hom_app,
    Iso.refl_hom]
  erw [Category.id_comp, Category.id_comp]
  exact h

end CategoryTheory

namespace ModuleCat

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The identification `Λ ⊗ ℤ/n ≅ Λ` sends `1 ⊗ 1` to `1`: its adjoint `ℤ/n ⟶ Λ` sends `1`
to `1`. -/
lemma extendScalarsAddCommGrpZModIso_hom_homEquiv {n : ℕ} (hn : (n : Λ) = 0) :
    ((extendScalarsAddCommGrpAdj Λ).homEquiv _ _ (extendScalarsAddCommGrpZModIso hn).hom).hom
      (ULift.up 1) = (1 : Λ) := by
  unfold extendScalarsAddCommGrpZModIso
  simp only [Iso.symm_hom, Iso.unop_inv, Functor.FullyFaithful.preimageIso_inv,
    Coyoneda.fullyFaithful_preimage, NatIso.ofComponents_inv_app, Equiv.toIso_inv_hom_apply,
    Quiver.Hom.unop_op, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  exact (AddCommGrpCat.zmodHomEquiv _ fun a : Λ ↦
    (Nat.cast_smul_eq_nsmul Λ n a).symm.trans (by rw [hn, zero_smul])).apply_symm_apply _

end ModuleCat

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The unit map `𝟙 ⟶ Res 𝟙` of the extension of scalars of sheaves of modules, the adjoint of its
unit comparison, is the unit of the lax monoidal restriction of scalars. -/
lemma extendScalarsAdjunction_homEquiv_η :
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv _ _
        (η (Sheaf.extendScalars X.smallEtaleTopology ρ)) =
      ε (Sheaf.restrictScalars X.smallEtaleTopology ρ) :=
  Equiv.apply_symm_apply _ _

/-- The unit map `Λ_X ⟶ Res Λ'_X` of the extension of scalars along `ρ`, read on global sections
through the constant sheaf adjunction, is `ρ` followed by the unit `Λ' ⟶ Γ(X, Λ'_X)`. -/
lemma constantSheafAdj_homEquiv_extendScalarsUnitMap :
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal).homEquiv _ _
        ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv (𝟙_ _) (𝟙_ _)
          (η (Sheaf.extendScalars X.smallEtaleTopology ρ))) =
      ε (ModuleCat.restrictScalars.{u + 1} ρ) ≫ (ModuleCat.restrictScalars ρ).map
        ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ')
          terminalIsTerminal).unit.app (𝟙_ _)) := by
  rw [extendScalarsAdjunction_homEquiv_η]
  exact constantSheafAdj_homEquiv_ε_sheafCompose _ _ _

variable {X} in
/-- The adjoint `ℤ/n ⟶ Γ(X, M)` of a morphism `Λ ⊗ ℤ/n ⟶ M` read through
`Λ ⊗ ℤ/n ≅ Λ_X` is obtained from the adjoint `Λ ⟶ Γ(X, M)` through `Λ ⊗ ℤ/n ≅ Λ`. -/
lemma homEquiv_extendScalarsConstantZModIso_hom_comp {n : ℕ} (hn : (n : Λ) = 0)
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ M) :
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).comp
        (extendScalarsAdjunction Λ X)).homEquiv _ _
        ((extendScalarsConstantZModIso X hn).hom ≫ g) =
      (ModuleCat.extendScalarsAddCommGrpAdj Λ).homEquiv _ _
        ((ModuleCat.extendScalarsAddCommGrpZModIso hn).hom ≫
          (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
            terminalIsTerminal).homEquiv _ _ g) := by
  rw [extendScalarsConstantZModIso, Iso.trans_hom, Iso.app_hom, Category.assoc,
    constantSheafCompExtendScalarsIso, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  simp only [Functor.mapIso_hom, NatIso.ofComponents_hom_app, Iso.refl_hom]
  erw [Category.comp_id]
  exact congrArg ((ModuleCat.extendScalarsAddCommGrpAdj Λ).homEquiv _ _)
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).homEquiv_naturality_left _ _)

variable {X} in
/-- The form of `AlgebraicGeometry.Etale.homEquiv_extendScalarsConstantZModIso_hom_comp` with the
two adjunctions applied one after the other. -/
lemma constantSheafAdj_homEquiv_extendScalarsAdjunction_homEquiv_zmod_comp {n : ℕ}
    (hn : (n : Λ) = 0) {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ⟶ M) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv _ _
        ((extendScalarsAdjunction Λ X).homEquiv _ _
          ((extendScalarsConstantZModIso X hn).hom ≫ g)) =
      (ModuleCat.extendScalarsAddCommGrpAdj Λ).homEquiv _ _
        ((ModuleCat.extendScalarsAddCommGrpZModIso hn).hom ≫
          (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
            terminalIsTerminal).homEquiv _ _ g) :=
  homEquiv_extendScalarsConstantZModIso_hom_comp hn g

variable {X} in
/-- The adjoint `ℤ/n ⟶ Γ(X, Λ_X)` of the identification `Λ ⊗ ℤ/n ≅ Λ_X`. -/
lemma constantSheafAdj_homEquiv_extendScalarsAdjunction_homEquiv_zmod {n : ℕ}
    (hn : (n : Λ) = 0) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv _ _
        ((extendScalarsAdjunction Λ X).homEquiv _ _ (extendScalarsConstantZModIso X hn).hom) =
      (ModuleCat.extendScalarsAddCommGrpAdj Λ).homEquiv _ _
        ((ModuleCat.extendScalarsAddCommGrpZModIso hn).hom ≫
          (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
            terminalIsTerminal).unit.app _) := by
  have h := constantSheafAdj_homEquiv_extendScalarsAdjunction_homEquiv_zmod_comp (X := X) hn (𝟙 _)
  rw [Category.comp_id, Adjunction.homEquiv_id] at h
  exact h

variable {X} in
/-- The adjoint `F ⟶ Res(Λ' ⊗ F)` of the change of coefficients `Λ ⊗ F ⟶ Res(Λ' ⊗ F)` is the unit
of the extension of scalars `Λ' ⊗ -`. -/
lemma extendScalarsAdjunction_homEquiv_changeMap_app_comp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')}
    (g : (extendScalars Λ' X).obj F ⟶ M) :
    (extendScalarsAdjunction Λ X).homEquiv _ _ ((extendScalarsChangeMap ρ X).app F ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).map g) =
      (extendScalarsAdjunction Λ' X).homEquiv _ _ g := by
  rw [Adjunction.homEquiv_naturality_right, extendScalarsChangeMap, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Adjunction.unit_naturality_assoc]
  rw [Category.assoc]
  congr 1
  have h := (extendScalarsAdjunction Λ X).right_triangle_components
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj ((extendScalars Λ' X).obj F))
  exact (h =≫ _).trans (Category.id_comp _)

/-- **The change of coefficients of `ℤ` is the unit map**: through `Λ ⊗ ℤ ≅ Λ_X` and
`Λ' ⊗ ℤ ≅ Λ'_X`, the change of coefficients `Λ ⊗ ℤ ⟶ Res(Λ' ⊗ ℤ)` is the unit map
`Λ_X ⟶ Res Λ'_X`, the adjoint of the unit comparison of the extension of scalars along `ρ`.
Blueprint: `det-sp-purity-coefficient-change`. -/
lemma extendScalarsConstantZModIso_inv_comp_changeMap_app_comp :
    (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).inv ≫
        (extendScalarsChangeMap ρ X).app X.constantSheafInt ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).map
          (extendScalarsConstantZModIso (Λ := Λ') X (n := 0) (by simp)).hom =
      (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).homEquiv (𝟙_ _) (𝟙_ _)
        (η (Sheaf.extendScalars X.smallEtaleTopology ρ)) := by
  rw [Iso.inv_comp_eq]
  apply ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).comp
    (extendScalarsAdjunction Λ X)).homEquiv _ _ |>.injective
  rw [homEquiv_extendScalarsConstantZModIso_hom_comp]
  erw [constantSheafAdj_homEquiv_extendScalarsUnitMap]
  simp only [Adjunction.comp_homEquiv]
  refine (congrArg ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv _ _)
      (extendScalarsAdjunction_homEquiv_changeMap_app_comp ρ _ _)).trans ?_
  have h := homEquiv_extendScalarsConstantZModIso_hom_comp (Λ := Λ') (X := X) (n := 0) (by simp)
    (𝟙 _)
  simp only [Category.comp_id, Adjunction.comp_homEquiv] at h
  refine h.trans ?_
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  apply (AddCommGrpCat.zmodHomEquiv _ fun a ↦ zero_nsmul a).injective
  simp only [AddCommGrpCat.zmodHomEquiv, Equiv.coe_fn_mk, AddCommGrpCat.hom_comp,
    AddMonoidHom.coe_comp, Function.comp_apply]
  erw [ModuleCat.extendScalarsAddCommGrpZModIso_hom_homEquiv,
    ModuleCat.extendScalarsAddCommGrpZModIso_hom_homEquiv]
  simp only [ModuleCat.forget₂_map, AddCommGrpCat.hom_ofHom, ModuleCat.hom_comp]
  exact (congrArg (fun x ↦ ((ModuleCat.restrictScalars ρ).map
    ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ') terminalIsTerminal).unit.app
      (𝟙_ _))).hom x) ((ModuleCat.restrictScalars_η ρ 1).trans (map_one ρ))).symm

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Transposing a morphism out of `f^* A_Y` through the identification `f^* A_Y ≅ A_X` of
constant sheaves (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`): global sections over `Y`
of the pushforward are global sections over `X`. -/
lemma constantSheafAdj_homEquiv_upperStarLowerStarAdjunction_homEquiv
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] (a : A) {M : Sheaf X.smallEtaleTopology A}
    (g : (constantSheaf X.smallEtaleTopology A).obj a ⟶ M) :
    (constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).homEquiv _ _
        ((upperStarLowerStarAdjunction A f).homEquiv _ _
          ((upperStarConstantSheafIso A f).hom.app a ≫ g)) =
      (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal).homEquiv _ _ g ≫
        (lowerStarCompSheafSectionsTerminalIso A f).inv.app M := by
  rw [← Iso.app_inv, Iso.eq_comp_inv, Iso.app_hom, upperStarConstantSheafIso]
  have h := Adjunction.homEquiv_ofNatIsoRight_apply
    ((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
      (upperStarLowerStarAdjunction A f)) (lowerStarCompSheafSectionsTerminalIso A f)
    (((((constantSheafAdj Y.smallEtaleTopology A terminalIsTerminal).comp
      (upperStarLowerStarAdjunction A f)).ofNatIsoRight
        (lowerStarCompSheafSectionsTerminalIso A f)).leftAdjointUniq
          (constantSheafAdj X.smallEtaleTopology A terminalIsTerminal)).hom.app a ≫ g)
  simp only [Adjunction.comp_homEquiv] at h
  refine h.symm.trans ?_
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit]

/-- Transposing a morphism out of `f^*(Λ ⊗ F)` through the identification
`f^*(Λ ⊗ F) ≅ Λ ⊗ f^* F` (`AlgebraicGeometry.Etale.upperStarExtendScalarsIso`). -/
lemma extendScalarsAdjunction_homEquiv_upperStarLowerStarAdjunction_homEquiv
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : (extendScalars Λ X).obj ((f)^*[AddCommGrpCat.{u + 1}].obj F) ⟶ M) :
    (extendScalarsAdjunction Λ Y).homEquiv _ _
        ((upperStarLowerStarAdjunction _ f).homEquiv _ _
          ((upperStarExtendScalarsIso Λ f).hom.app F ≫ g)) =
      (upperStarLowerStarAdjunction _ f).homEquiv _ _
        ((extendScalarsAdjunction Λ X).homEquiv _ _ g) := by
  have h := Adjunction.homEquiv_naturality_right
    ((extendScalarsAdjunction Λ Y).comp (upperStarLowerStarAdjunction _ f))
    ((upperStarExtendScalarsIso Λ f).hom.app F) g
  rw [upperStarExtendScalarsIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply] at h
  simp only [NatIso.ofComponents_hom_app, Iso.refl_hom] at h
  erw [Category.comp_id] at h
  exact h

/-- The identifications `Λ ⊗ ℤ ≅ Λ` are compatible with the pullback along `f : X ⟶ Y`: through
`f^*(Λ ⊗ ℤ_Y) ≅ Λ ⊗ ℤ_X` and `f^* Λ_Y ≅ Λ_X`. -/
lemma upperStarExtendScalarsConstantSheafIntIso_hom_comp :
    (upperStarExtendScalarsConstantSheafIntIso Λ f).hom ≫
        (extendScalarsConstantZModIso (Λ := Λ) X (n := 0) (by simp)).hom =
      (f)^*[ModuleCat.{u + 1} Λ].map
          (extendScalarsConstantZModIso (Λ := Λ) Y (n := 0) (by simp)).hom ≫
        (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app (ModuleCat.of Λ Λ) := by
  apply (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ |>.injective
  apply (extendScalarsAdjunction Λ Y).homEquiv _ _ |>.injective
  apply (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv _ _ |>.injective
  rw [upperStarExtendScalarsConstantSheafIntIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc, extendScalarsAdjunction_homEquiv_upperStarLowerStarAdjunction_homEquiv,
    Adjunction.homEquiv_naturality_left, Iso.app_hom]
  erw [constantSheafAdj_homEquiv_upperStarLowerStarAdjunction_homEquiv]
  rw [Adjunction.homEquiv_naturality_left]
  rw [constantSheafAdj_homEquiv_extendScalarsAdjunction_homEquiv_zmod,
    constantSheafAdj_homEquiv_extendScalarsAdjunction_homEquiv_zmod_comp,
    ← Category.comp_id ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) f).hom.app _)]
  erw [constantSheafAdj_homEquiv_upperStarLowerStarAdjunction_homEquiv]
  rw [Adjunction.homEquiv_id, ← Category.assoc, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  rfl

end Pullback

end AlgebraicGeometry.Etale
