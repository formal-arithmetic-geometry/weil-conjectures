/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.CoherentLocalFinitePresentation
import WeilConjectures.AlgebraicGeometry.HomLocalKernelOfPresentation

/-!
# Local kernel models for Hom out of a coherent module

Stacks Project, Tags 01BW and 01CQ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace AlgebraicGeometry.Scheme.Modules

/-- For any target module, Hom out of a coherent source is locally a kernel between finite
sums of the target. No coherence assumption on the target is needed
(Stacks, Tags 01BW, 01CQ and 01CP). -/
theorem homObj_locally_kernel_of_coherent (X : Scheme.{u}) (G F : X.Modules)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ (m n : ℕ)
      (α : (⨁ fun _ : Fin n ↦ F.restrict U.ι) ⟶
        (⨁ fun _ : Fin m ↦ F.restrict U.ι)),
      Nonempty ((restrictFunctor U.ι).obj
        (SheafOfModules.homObj (R := X.sheaf) G F) ≅ kernel α) := by
  obtain ⟨V, hxV, m, n, a, ⟨e⟩⟩ := coherent_local_finite_presentation X G hG x
  obtain ⟨α, hα⟩ := homObj_locally_kernel_of_local_presentation X G F V m n a e
  exact ⟨V, hxV, m, n, α, hα⟩

end AlgebraicGeometry.Scheme.Modules
