/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable

/-!
# Cokernels of monomorphisms between dualizable objects are dualizable in `D(A)`

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` a short exact sequence in `A` with `X₁` and `X₂`
dualizable. Then `X₃`, placed in degree zero, is dualizable in the derived category `D(A)`
(`DerivedCategory.isDualizable_singleFunctor_obj_of_shortExact`): it is quasi-isomorphic to the
mapping cone of `X₁[0] ⟶ X₂[0]`, a bounded complex of dualizable objects.

The intended application is the constant complex `(Λ/ϖⁿ)_X` on a site, for a nonzerodivisor `ϖ`
of the coefficient ring `Λ`: it is the cokernel of `ϖⁿ : Λ_X ⟶ Λ_X`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

section Zero

variable {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C]

/-- A zero object of a preadditive monoidal category is dualizable, with itself as dual and
zero evaluation and coevaluation: both zig-zag identities are endomorphisms of an object
isomorphic to the zero object. -/
theorem IsZero.isDualizable {Z : C} (hZ : IsZero Z) : IsDualizable Z :=
  ⟨{ rightDual := Z
     exact :=
      { coevaluation' := 0
        evaluation' := 0
        coevaluation_evaluation' := (hZ.of_iso (ρ_ Z)).eq_of_src _ _
        evaluation_coevaluation' := (hZ.of_iso (λ_ Z)).eq_of_src _ _ } }⟩

/-- The biproduct of a dualizable object with a zero object is dualizable. -/
theorem IsDualizable.biprod_of_isZero_right [HasBinaryBiproducts C] {P Z : C}
    (hP : IsDualizable P) (hZ : IsZero Z) : IsDualizable (P ⊞ Z) :=
  hP.of_iso
    { hom := biprod.inl
      inv := biprod.fst
      hom_inv_id := by simp
      inv_hom_id := by
        rw [← biprod.total, hZ.eq_of_tgt biprod.snd 0, zero_comp, add_zero] }

/-- The biproduct of a zero object with a dualizable object is dualizable. -/
theorem IsDualizable.biprod_of_isZero_left [HasBinaryBiproducts C] {P Z : C}
    (hP : IsDualizable P) (hZ : IsZero Z) : IsDualizable (Z ⊞ P) :=
  hP.of_iso
    { hom := biprod.inr
      inv := biprod.snd
      hom_inv_id := by simp
      inv_hom_id := by
        rw [← biprod.total, hZ.eq_of_tgt biprod.fst 0, zero_comp, zero_add] }

end Zero

section Retract

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A retract of an object with a right dual has a right dual when idempotents split: the dual is
the image of the idempotent `(r ≫ i)ᘁ` on the dual. -/
theorem nonempty_hasRightDual_of_retract [IsIdempotentComplete C] {R D : C} (h : Retract R D)
    [HasRightDual D] : Nonempty (HasRightDual R) := by
  have he : ((h.r ≫ h.i)ᘁ) ≫ ((h.r ≫ h.i)ᘁ) = (h.r ≫ h.i)ᘁ := by
    rw [← comp_rightAdjointMate, Category.assoc, h.retract_assoc]
  obtain ⟨S, s, p, hsp, hps⟩ := IsIdempotentComplete.idempotents_split _ _ he
  have k1 : ((p ≫ s) ⊗ₘ h.i) ≫ ε_ D Dᘁ = (Dᘁ ◁ h.i) ≫ ε_ D Dᘁ := by
    rw [hps, tensorHom_def', Category.assoc, rightAdjointMate_comp_evaluation,
      ← whiskerLeft_comp_assoc, h.retract_assoc]
  have k2 : η_ D Dᘁ ≫ ((h.r ≫ h.i) ⊗ₘ p) = η_ D Dᘁ ≫ (D ◁ p) := by
    rw [tensorHom_def, ← Category.assoc, ← coevaluation_comp_rightAdjointMate, Category.assoc,
      ← whiskerLeft_comp, ← hps, Category.assoc, hsp, Category.comp_id]
  exact ⟨
    { rightDual := S
      exact :=
        { coevaluation' := η_ D Dᘁ ≫ (h.r ⊗ₘ p)
          evaluation' := (s ⊗ₘ h.i) ≫ ε_ D Dᘁ
          coevaluation_evaluation' := by
            calc S ◁ (η_ D Dᘁ ≫ (h.r ⊗ₘ p)) ≫ (α_ S R S).inv ≫ ((s ⊗ₘ h.i) ≫ ε_ D Dᘁ) ▷ S
                = S ◁ η_ D Dᘁ ≫ (α_ S D Dᘁ).inv ≫ ((s ⊗ₘ (h.r ≫ h.i)) ⊗ₘ p) ≫
                  ε_ D Dᘁ ▷ S := by
                  rw [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
                  congr 1
                  rw [← id_tensorHom, associator_inv_naturality_assoc, ← tensorHom_id,
                    ← tensorHom_id, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
                  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
              _ = s ▷ _ ≫ Dᘁ ◁ (η_ D Dᘁ ≫ ((h.r ≫ h.i) ⊗ₘ p)) ≫ (α_ Dᘁ D S).inv ≫
                  ε_ D Dᘁ ▷ S := by
                  have e : (α_ S D Dᘁ).inv ≫ ((s ⊗ₘ (h.r ≫ h.i)) ⊗ₘ p) =
                      (s ⊗ₘ ((h.r ≫ h.i) ⊗ₘ p)) ≫ (α_ Dᘁ D S).inv :=
                    (associator_inv_naturality _ _ _).symm
                  rw [reassoc_of% e, tensorHom_def, Category.assoc, whisker_exchange_assoc]
                  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
              _ = s ▷ _ ≫ Dᘁ ◁ η_ D Dᘁ ≫ Dᘁ ◁ (D ◁ p) ≫ (α_ Dᘁ D S).inv ≫ ε_ D Dᘁ ▷ S := by
                  rw [k2, MonoidalCategory.whiskerLeft_comp, Category.assoc]
              _ = s ▷ _ ≫ Dᘁ ◁ η_ D Dᘁ ≫ (α_ Dᘁ D Dᘁ).inv ≫ ε_ D Dᘁ ▷ Dᘁ ≫ 𝟙_ C ◁ p := by
                  rw [associator_inv_naturality_right_assoc, whisker_exchange]
              _ = _ := by
                  rw [ExactPairing.coevaluation_evaluation_assoc, whiskerRight_id, id_whiskerLeft]
                  simp [reassoc_of% hsp]
          evaluation_coevaluation' := by
            calc (η_ D Dᘁ ≫ (h.r ⊗ₘ p)) ▷ R ≫ (α_ R S R).hom ≫ R ◁ ((s ⊗ₘ h.i) ≫ ε_ D Dᘁ)
                = η_ D Dᘁ ▷ R ≫ (α_ D Dᘁ R).hom ≫ (h.r ⊗ₘ (((p ≫ s) ⊗ₘ h.i) ≫ ε_ D Dᘁ)) := by
                  rw [comp_whiskerRight, Category.assoc, MonoidalCategory.whiskerLeft_comp]
                  congr 1
                  rw [← tensorHom_id, associator_naturality_assoc, ← id_tensorHom, ← id_tensorHom,
                    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
                  simp only [Category.comp_id, Category.id_comp, tensorHom_comp_tensorHom]
              _ = η_ D Dᘁ ▷ R ≫ (α_ D Dᘁ R).hom ≫ D ◁ (Dᘁ ◁ h.i) ≫ D ◁ ε_ D Dᘁ ≫
                  h.r ▷ _ := by
                  rw [k1, tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc]
              _ = 𝟙_ C ◁ h.i ≫ η_ D Dᘁ ▷ D ≫ (α_ D Dᘁ D).hom ≫ D ◁ ε_ D Dᘁ ≫ h.r ▷ _ := by
                  rw [← associator_naturality_right_assoc, whisker_exchange_assoc]
              _ = _ := by
                  rw [ExactPairing.evaluation_coevaluation_assoc, id_whiskerLeft, whiskerRight_id]
                  simp [h.retract_assoc] } }⟩

/-- A retract of a dualizable object is dualizable when idempotents split. -/
theorem IsDualizable.of_retract [IsIdempotentComplete C] {R D : C} (h : Retract R D)
    (hD : IsDualizable D) : IsDualizable R := by
  obtain ⟨_⟩ := hD
  exact nonempty_hasRightDual_of_retract h

end Retract

end CategoryTheory

namespace DerivedCategory

section

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]

/-- The mapping cone of a morphism `X₁[0] ⟶ X₂[0]` of complexes concentrated in degree zero
has its terms of degree `-1` and `0` dualizable as soon as `X₁` and `X₂` are, and all other
terms zero. -/
lemma isDualizable_mappingCone_single_X {X₁ X₂ : A} (h₁ : IsDualizable X₁)
    (h₂ : IsDualizable X₂)
    (φ : (HomologicalComplex.single A (.up ℤ) 0).obj X₁ ⟶
      (HomologicalComplex.single A (.up ℤ) 0).obj X₂) (n : ℤ) :
    IsDualizable ((CochainComplex.mappingCone φ).X n) := by
  refine IsDualizable.of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ n (n + 1) rfl).symm ?_
  by_cases hn : n = -1
  · subst hn
    refine IsDualizable.biprod_of_isZero_right ?_
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide))
    exact h₁.of_iso (HomologicalComplex.singleObjXIsoOfEq _ 0 X₁ (-1 + 1) rfl).symm
  by_cases hn' : n = 0
  · subst hn'
    refine IsDualizable.biprod_of_isZero_left ?_
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by decide))
    exact h₂.of_iso (HomologicalComplex.singleObjXSelf _ 0 X₂).symm
  · refine IsDualizable.biprod_of_isZero_left (IsZero.isDualizable ?_) ?_
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn'
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)

end

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

/-- **The cokernel of a monomorphism between dualizable objects is dualizable in `D(A)`.** For
a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` in `A` with `X₁` and `X₂` dualizable, the complex
`X₃[0]` is dualizable in `D(A)`: it is quasi-isomorphic to the mapping cone of
`X₁[0] ⟶ X₂[0]` (`CochainComplex.mappingCone.quasiIso_descShortComplex`), a complex
concentrated in degrees `-1` and `0` with dualizable terms
(`DerivedCategory.isDualizable_Q_obj`). -/
theorem isDualizable_singleFunctor_obj_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : IsDualizable S.X₁) (h₂ : IsDualizable S.X₂) :
    IsDualizable ((singleFunctor A 0).obj S.X₃) := by
  let S' := S.map (HomologicalComplex.single A (.up ℤ) 0)
  have hS' : S'.ShortExact := hS.map_of_exact _
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have : (CochainComplex.mappingCone S'.f).IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  have : (CochainComplex.mappingCone S'.f).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia),
      HomologicalComplex.isZero_single_obj_X _ _ _ _ (by lia)⟩
  exact (isDualizable_Q_obj _ (-1) 0 (isDualizable_mappingCone_single_X h₁ h₂ S'.f)).of_iso
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S')) ≪≫
      ((singleFunctorIsoCompQ A 0).app S.X₃).symm)

end DerivedCategory
