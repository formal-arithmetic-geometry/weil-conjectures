/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomTensorDegreewise
import WeilConjectures.Algebra.Homology.HomTensorDifferentialComponent
import WeilConjectures.Algebra.Homology.HomComplexProjections

/-!
# Degreewise currying for the Hom-total-tensor comparison

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

set_option synthInstance.maxSize 256 in
/-- Degreewise currying commutes with the Hom-complex differentials. -/
theorem homTensorDegreewiseMap_comm (K L M : CochainComplex Mod ℤ) (n m : ℤ) :
    letI := SheafOfModules.monoidalCategory R
    homTensorDegreewiseMap R K L M n ≫
        (homComplex (R := R)
          (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).d n m =
      (homComplex (R := R) K (homComplex (R := R) L M)).d n m ≫
        homTensorDegreewiseMap R K L M m := by
  let _ := SheafOfModules.monoidalCategory R
  by_cases h : n + 1 = m
  · subst m
    let T := CochainComplex.mapBifunctor K L (curriedTensor Mod)
    have hs := Classical.choose_spec
      (homComplex_projections_exists.{u, v, max u v, max u v} (J := J) (R := R))
    apply Limits.Fan.IsLimit.hom_ext (hs.1 T M (n + 1)).some
    intro t
    change (homTensorDegreewiseMap R K L M n ≫
        (homComplex (R := R) T M).d n (n + 1)) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl =
      ((homComplex (R := R) K (homComplex (R := R) L M)).d n (n + 1) ≫
        homTensorDegreewiseMap R K L M (n + 1)) ≫
          homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl
    have hd := hs.2.1 T M n (n + 1) t (t + (n + 1)) (t + n) (t + 1)
      rfl rfl rfl (by omega)
    change (homComplex (R := R) T M).d n (n + 1) ≫
        homTensorProjection R T M (n + 1) t (t + (n + 1)) rfl =
      homTensorProjection R T M n t (t + n) rfl ≫
        SheafOfModules.homObjMap (R := R) (𝟙 (T.X t)) (M.d (t + n) (t + (n + 1))) -
      n.negOnePow • (homTensorProjection R T M n (t + 1) (t + (n + 1)) (by omega) ≫
        SheafOfModules.homObjMap (R := R) (T.d t (t + 1))
          (𝟙 (M.X (t + (n + 1))))) at hd
    rw [Category.assoc, hd, Preadditive.comp_sub, Linear.comp_units_smul]
    simpa only [Category.assoc] using
      (homTensorDegreewiseMap_iteratedDifferential_component R K L M n t).symm
  · rw [((homComplex (R := R)
        (CochainComplex.mapBifunctor K L (curriedTensor Mod)) M).shape n m
      (by simpa [ComplexShape.up_Rel] using h)),
      ((homComplex (R := R) K (homComplex (R := R) L M)).shape n m
      (by simpa [ComplexShape.up_Rel] using h)),
      Limits.HasZeroMorphisms.comp_zero, Limits.HasZeroMorphisms.zero_comp]

end CategoryTheory
