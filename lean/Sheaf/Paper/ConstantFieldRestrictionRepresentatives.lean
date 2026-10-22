/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteFieldDerivedTensorComparison
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB

/-! # Restriction of flat K-flat representatives over constant fields

Source: Stacks Project, Tags 0C2X, 03EK, 0GMW, 06YN and 06YU.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct ZeroObject

namespace FiniteFieldDerivedTensor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v}]
  (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]

private theorem field_representatives (A : Type (max u v)) [Field A]
    (P : Complexes J A) : representatives J A P := by
  let R := coefficients J A
  let 𝒜 := Modules J A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  have (M : 𝒜) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : 𝒜) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : ∀ X₁ X₂ : GradedObject ℤ 𝒜, GradedObject.HasTensor X₁ X₂ := by
    infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ 𝒜,
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ : GradedObject ℤ 𝒜,
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance
  have : ∀ X₁ X₂ X₃ X₄ : GradedObject ℤ 𝒜,
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := by infer_instance
  have : AB5OfSize.{max u v, max u v} AddCommGrpCat.{max u v} := inferInstance
  have : AB5OfSize.{0, 0} AddCommGrpCat.{max u v} := AB5OfSize_shrink _
  have : HasExactColimitsOfShape ℤ 𝒜 :=
    HasExactColimitsOfShape.domain_of_functor ℤ (SheafOfModules.toSheaf _)
  have hflat (N : 𝒜) : ObjectProperty.flat N :=
    SheafOfModules.flat_to_cat R N (SheafOfModules.isFlat_constantFieldModule J A N)
  have hk : (HomologicalComplex.quasiIso 𝒜 (.up ℤ)).kFlat P := by
    apply ObjectProperty.prop_of_isColimit _ P.isColimitFiltrationLECocone
    intro n
    exact CochainComplex.kFlat_of_isStrictlyLE_of_flat (P.truncLE n) n (fun i ↦ hflat _)
  refine ⟨?_, fun n ↦ (hflat (P.X n)).2⟩
  intro Z hZ
  let T := MonoidalCategory.tensorRight P
  have hz : QuasiIso (0 : (0 : CochainComplex 𝒜 ℤ) ⟶ Z) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex 𝒜 ℤ) ⟶ Z)) := hk.2 _ hz
  have htzero : (T.obj (0 : CochainComplex 𝒜 ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex 𝒜 ℤ) ⟶ Z)) i).1 (htzero i)

/-- Restriction along a field extension preserves K-flat representatives with flat terms.
Source: Stacks Project, Tags 03EK, 06YN and 06YT
(blueprint: lem-pur-constant-field-restriction-representatives).
Proof: every module sheaf over a constant field is flat, by the local relation
criterion. Hence every term of every good upper truncation is flat, including its
cycle sheaf in the top degree. A bounded-above flat complex is K-flat. The upper
truncations have the original complex as their filtered colimit, and K-flatness is
closed under this colimit because sheaf tensor preserves colimits and filtered
colimits of module sheaves are exact. Thus every complex over the constant field F
is K-flat with flat terms. Apply this to the restricted complex. No finiteness,
boundedness, nonzero-section or nonempty-site assumption is used. -/
theorem restriction_preserves_representatives (K : Complexes J B)
    (_hK : representatives J B K) :
    representatives J F ((restrictComplex J F B).obj K) := by
  exact field_representatives J F ((restrictComplex J F B).obj K)

end FiniteFieldDerivedTensor
