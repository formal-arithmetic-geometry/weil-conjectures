/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # The Koszul resolution of a quotient

Source: Stacks Project, Tags 0623, 062E and 0BQZ.
(blueprint: new-j3-koszul-projective-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

-- The degree-one calculation follows the proof in KoszulRegularSequenceDualComplex;
-- importing that module here would create a cycle through KoszulExtDualHomology.
private theorem koszulBoundary_zero_quotient_formula
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (x : ⋀[A]^1 (Fin r →₀ A)) :
    exteriorPower.zeroEquiv A (Fin r →₀ A) (koszulBoundary A r f 0 x) =
      Finsupp.linearCombination A f (exteriorPower.oneEquiv A (Fin r →₀ A) x) := by
  have he : (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap.comp
      (koszulBoundary A r f 0) = (Finsupp.linearCombination A f).comp
        (exteriorPower.oneEquiv A (Fin r →₀ A)).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext v
    have hg : koszulBoundary A r f 0 (exteriorPower.ιMulti A 1 v) =
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm
          (Finsupp.linearCombination A f (v 0)) := by
      apply Subtype.ext
      simp [koszulBoundary, exteriorPower.zeroEquiv_symm_apply,
        ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
        Algebra.algebraMap_eq_smul_one]
    simp [hg]
  exact LinearMap.congr_fun he x

end ExteriorAlgebra
