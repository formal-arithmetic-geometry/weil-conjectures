/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsionKernel
import WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsionCoker

/-! # Torsion bounds for reductions of coherent maps

Source: Stacks Project, Remark 0888.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Reduction by any positive ideal power doubles an actual kernel/cokernel bound
(Stacks, Tag 0888). -/
theorem coherentMap_reduction_torsion
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F H : CoherentModules X) (a : F ⟶ H) (t : ℕ) (ht : 1 ≤ t)
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (kernel a.hom)))
    (hcoker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (cokernel a.hom))) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by
  intro n
  exact ⟨coherentMap_reduction_torsion_kernel I K F H a t ht hker hcoker n,
    coherentMap_reduction_torsion_coker I K F H a t ht hker hcoker n⟩

end AlgebraicGeometry
