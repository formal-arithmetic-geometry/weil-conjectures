/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ConeHorizontalProjection
public import WeilConjectures.Algebra.Homology.ConeHorizontalStepStable
import WeilConjectures.Algebra.Homology.HorizontalProjectionNaturality
import WeilConjectures.Algebra.Homology.HorizontalProjectionTailDifferential

/-! # Generator calculation for the signed column projection

## References

* Stacks Project, Homology, Tag 012X (Lemma 12.25.1(1))
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- Cone source differential with a transported successor degree. -/
private theorem inl_d_eq {F G : CochainComplex C ℤ} (q : F ⟶ G)
    (i j : ℤ) (hj : i + 1 = j) :
    HomologicalComplex.homotopyCofiber.inlX q (i + 1) i rfl ≫
      HomologicalComplex.homotopyCofiber.d q i j =
    (F.XIsoOfEq hj).hom ≫
      (-F.d j (j + 1) ≫ HomologicalComplex.homotopyCofiber.inlX q (j + 1) j rfl +
        q.f j ≫ HomologicalComplex.homotopyCofiber.inrX q j) := by
  subst j
  simpa using HomologicalComplex.homotopyCofiber.inlX_d q i (i + 1)
    ((i + 1) + 1) rfl rfl

variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- Source block of the signed projection. -/
@[reassoc]
private theorem inl_coneHorizontalProjection
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat) (n + 1) n rfl ≫ coneHorizontalProjection f p n =
    ((-1 : ℤ) ^ p) • (horizontalExtendedProjection A p (n + 1) ≫
      (((A.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show n + 1 - (p : ℤ) = (n + -(p : ℤ)) + 1 by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat)
        ((n + -(p : ℤ)) + 1) (n + -(p : ℤ)) rfl) := by
  simp [coneHorizontalProjection]

/-- Target block of the signed projection. -/
@[reassoc]
private theorem inr_coneHorizontalProjection
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (CochainComplex.mappingCone.inr
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).f n ≫ coneHorizontalProjection f p n =
    horizontalExtendedProjection B p n ≫
      (((B.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show n - (p : ℤ) = n + -(p : ℤ) by omega)).hom ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat)).f
        (n + -(p : ℤ)) := by
  change HomologicalComplex.homotopyCofiber.inrX _ n ≫ _ = _
  simp [coneHorizontalProjection]

@[reassoc]
private theorem inrX_coneHorizontalProjection
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    HomologicalComplex.homotopyCofiber.inrX
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat) n ≫ coneHorizontalProjection f p n =
    horizontalExtendedProjection B p n ≫
      (((B.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show n - (p : ℤ) = n + -(p : ℤ) by omega)).hom ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat)).f
        (n + -(p : ℤ)) := by
  exact inr_coneHorizontalProjection f p n

/-- The differential defect of the signed column projection vanishes on each
source and target generator with horizontal index at least `p`. -/
theorem coneHorizontal_projection_generator_vanishing
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (∀ h : ℕ, p ≤ h →
      (coneHorizontalSummand A h (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inlX
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat) (n + 1) n rfl) ≫
        (coneHorizontalProjection f p n ≫
          ((CochainComplex.mappingCone
            (HomologicalComplex.extendMap (f.f p)
              ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).d n (n + 1) -
          (CochainComplex.mappingCone
            (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
              ComplexShape.embeddingUpNat)).d n (n + 1) ≫
            coneHorizontalProjection f p (n + 1)) = 0) ∧
    (∀ h : ℕ, p ≤ h →
      (coneHorizontalSummand B h n ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat)).f n) ≫
        (coneHorizontalProjection f p n ≫
          ((CochainComplex.mappingCone
            (HomologicalComplex.extendMap (f.f p)
              ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).d n (n + 1) -
          (CochainComplex.mappingCone
            (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
              ComplexShape.embeddingUpNat)).d n (n + 1) ≫
            coneHorizontalProjection f p (n + 1)) = 0) := by
  constructor
  · intro h hp
    rw [CategoryTheory.Preadditive.comp_sub]
    apply sub_eq_zero.mpr
    simp only [Category.assoc, inl_coneHorizontalProjection_assoc]
    rw [CochainComplex.shiftFunctor_obj_d']
    simp only [CategoryTheory.Linear.comp_units_smul,
      CategoryTheory.Preadditive.zsmul_comp]
    change _ = coneHorizontalSummand A h (n + 1) ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat) (n + 1) n rfl ≫
        HomologicalComplex.homotopyCofiber.d _ n (n + 1) ≫ _
    rw [HomologicalComplex.homotopyCofiber.inlX_d_assoc _ n (n + 1)
      ((n + 1) + 1) rfl rfl]
    simp only [CategoryTheory.Preadditive.add_comp,
      CategoryTheory.Preadditive.comp_add, CategoryTheory.Preadditive.neg_comp,
      CategoryTheory.Preadditive.comp_neg, Category.assoc,
      inl_coneHorizontalProjection]
    erw [inl_d_eq _ (n + -(p : ℤ)) (n + 1 + -(p : ℤ)) (by omega)]
    simp only [CategoryTheory.Preadditive.comp_add, CategoryTheory.Preadditive.comp_neg,
      CategoryTheory.Preadditive.comp_zsmul,
      HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
      Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast]
    erw [inrX_coneHorizontalProjection f p (n + 1)]
    have he : (-1 : ℤ) ^ p * (-1 : ℤ) ^ p = 1 := by
      rw [← mul_pow]
      norm_num
    simp only [smul_smul, he, one_smul]
    apply congrArg₂ (· + ·)
    · erw [horizontalProjection_tail_differential_assoc A p h (n + 1)
        (n + 1 + -(p : ℤ)) (n + 1 + -(p : ℤ) + 1) (by omega) (by omega) hp]
      simp only [CategoryTheory.Preadditive.zsmul_comp, smul_smul, he, one_smul, Category.assoc]
    · erw [horizontalProjection_naturality_assoc f p (n + 1)
        (n + 1 + -(p : ℤ)) (by omega)]
      rfl
  · intro h hp
    rw [CategoryTheory.Preadditive.comp_sub]
    apply sub_eq_zero.mpr
    simp only [Category.assoc, inr_coneHorizontalProjection_assoc]
    rw [CochainComplex.shiftFunctor_obj_d']
    simp only [CategoryTheory.Linear.comp_units_smul]
    rw [CochainComplex.mappingCone.inr_f_d]
    rw [HomologicalComplex.Hom.comm_assoc]
    simp only [inr_coneHorizontalProjection]
    have hd := horizontalProjection_tail_differential B p h n
      (n + -(p : ℤ)) (n + 1 + -(p : ℤ)) (by omega) (by omega) hp
    have he := congrArg (fun a ↦ a ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat)).f
          (n + 1 + -(p : ℤ))) hd
    simpa only [Category.assoc, CategoryTheory.Preadditive.zsmul_comp,
      CategoryTheory.Linear.units_smul_comp, Units.smul_def, Int.negOnePow_neg,
      Int.coe_negOnePow_natCast] using he.symm

end HomologicalComplex₂
