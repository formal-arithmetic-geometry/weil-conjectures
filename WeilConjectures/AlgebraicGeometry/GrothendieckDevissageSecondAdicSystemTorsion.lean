/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import WeilConjectures.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicTorsionKernel
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicTorsionCokernel

/-! # Uniform torsion bound for a compatible second-ideal algebraization

## References

* [Stacks Project, Tags 088A, 0888]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A fixed compatible algebraization has the uniform exponent 4t.
There is no existence conclusion: N, δ and σ are supplied, and no projection
characterization of θ is needed for this estimate. (Stacks, Tags 088A and 0888) -/
theorem grothendieckDevissage_secondAdicSystem_torsion
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip)
    (hsquare : ∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n))
    (t : ℕ) (ht : 1 ≤ t)
    (hα : ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n))))) :
    ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (4 * t)).2
        (cokernel (δ.hom.app (op e)))) := by
  intro e
  exact ⟨
    grothendieckDevissage_secondAdicSystem_torsion_kernel I K M hthick H α θ N δ σ
      hsquare t ht hα e,
    grothendieckDevissage_secondAdicSystem_torsion_cokernel I K M hthick H α θ N δ σ
      hsquare t ht hα e⟩

end AlgebraicGeometry
