/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilatedLimitScalar
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal

/-! # From termwise annihilation to annihilation of an affine limit

## References

* Stacks Project, Tag 0888
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Uniform termwise annihilation gives exponent `2 * t` on an affine inverse-limit map
(Stacks, Tags 0888 and 087W). -/
theorem coherentFormalModule_annihilated_affine_limit
    (X : Scheme.{u}) [IsNoetherian X] (I K : X.IdealSheafData)
    (F G : CoherentFormalModule X I) (α : F ⟶ G) (t : ℕ) (ht : 1 ≤ t)
    (h : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) (U : X.affineOpens) :
    K.ideal U ^ (2 * t) ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
      (lim.map (Functor.whiskerRight α.hom
        (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) ∧
    K.ideal U ^ (2 * t) ≤ Module.annihilator Γ(X, U.1)
      (↥(limit (G.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :
        ModuleCat Γ(X, U.1)) ⧸ LinearMap.range
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) := by
  let v := (lim.map (Functor.whiskerRight α.hom
    (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom
  have hv := coherentFormalModule_affine_limit_scalar_composites X I K F G α t ht h U
  simpa [v] using LinearMap.annihilated_of_scalar_composites (K.ideal U) t v hv

end AlgebraicGeometry
