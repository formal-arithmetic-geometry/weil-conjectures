/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModel
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Bounded cohomology over a constant field has the same Tor bound

## References

* Stacks Project, Tags 03ER, 08FC, 08G0 and 08G1
* Bhatt--Scholze, Remark 6.3.2
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Over a constant field sheaf every module is flat, so a bounded object has the same
Tor interval (Stacks, Tags 03ER, 08FC, 08G0 and 08G1; Bhatt--Scholze, Remark 6.3.2). -/
theorem coefficientFieldTorBounds {C : Type w} [SmallCategory C]
    (J : GrothendieckTopology C) (k : Type w) [Field k]
    (K : ConstantCompletion.D (ConstantCompletion.constant J k))
    (a b : ℤ) (hab : a ≤ b)
    (h : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((coefficientModelCohomology _ q).obj K)) :
    HasCoefficientModelTorAmplitude _ K a b := by
  let R := ConstantCompletion.constant J k
  let := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  have : K.IsGE a := (DerivedCategory.isGE_iff _ a).mpr
    (fun q hq ↦ h q (Or.inl hq))
  have : K.IsLE b := (DerivedCategory.isLE_iff _ b).mpr
    (fun q hq ↦ h q (Or.inr hq))
  obtain ⟨P, hPa, hPb, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE K a b
  apply (coefficientModelTorAmplitude_iff_flatModel R K a b hab).mpr
  refine ⟨P, hPa, hPb, fun i ↦ ?_, ⟨e.symm⟩⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (P.X i))
    (SheafOfModules.isFlat_constantFieldModule J k (P.X i))

end CategoryTheory
