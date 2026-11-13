/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafPositiveContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafDegreeZeroFactorization

/-! # The singleton signed insertion contraction

Source: Stacks Project, Tags 02FU and 01FM.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The singleton projection admits the signed insertion contraction (Stacks, Tags 02FU and 01FM).
-/
theorem alternatingCechSheafAugmentation_restrict_singleton_contraction
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    let a : A ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
        ComplexShape.embeddingUpNat)
    ∃ π : C.X 0 ⟶ A.X 0,
      ∃ h : ∀ k : ℤ, C.X (k + 1) ⟶ C.X k,
        (C.d (0 : ℤ) (0 + 1) ≫ h 0 + π ≫ a.f 0 = 𝟙 (C.X 0)) ∧
        ∀ k : ℤ, 0 < k → C.d k (k + 1) ≫ h k +
          (C.XIsoOfEq (show k = k - 1 + 1 by omega)).hom ≫
            h (k - 1) ≫ C.d (k - 1) k = 𝟙 (C.X k) := by
  dsimp only
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let A := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((CochainComplex.single₀ X.Modules).obj G).extend ComplexShape.embeddingUpNat)
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
  let a : A ⟶ C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
    (HomologicalComplex.extendMap (alternatingCechSheafAugmentation U G)
      ComplexShape.embeddingUpNat)
  obtain ⟨h, hpos⟩ := alternatingCechSheaf_restrict_positive_contraction U G i
  change ∀ k : ℤ, C.X (k + 1) ⟶ C.X k at h
  let d₀ := C.d 0 (0 + 1)
  let d₁ := C.d (0 + 1) ((0 + 1) + 1)
  have h1 : d₁ ≫ h (0 + 1) + h 0 ≫ d₀ = 𝟙 (C.X (0 + 1)) := by
    simpa [d₀, d₁, C, F] using hpos 1 (by norm_num)
  have hd : (𝟙 (C.X 0) - d₀ ≫ h 0) ≫ d₀ = 0 := by
    have he := congrArg (fun f ↦ d₀ ≫ f) h1
    have hs : d₀ ≫ d₁ = 0 := C.d_comp_d _ _ _
    simp only [Preadditive.comp_add, ← Category.assoc, hs,
      Limits.zero_comp, zero_add, Category.comp_id] at he
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc]
    rw [Category.assoc] at he
    exact sub_eq_zero.mpr he.symm
  obtain ⟨π, hπ⟩ := alternatingCechSheafAugmentation_restrict_degreeZero_factorization
    U G i (𝟙 (C.X 0) - d₀ ≫ h 0) (by simpa [d₀, C, F] using hd)
  refine ⟨π, h, ?_, hpos⟩
  change d₀ ≫ h 0 + π ≫ a.f 0 = 𝟙 (C.X 0)
  rw [hπ]
  abel

end AlgebraicGeometry
