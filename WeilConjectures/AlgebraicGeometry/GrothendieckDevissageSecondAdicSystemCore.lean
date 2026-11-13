/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLift
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemTorsion

/-! # Algebraization after a supplied quotient interchange

## References

* [Stacks Project, Tags 088A, 0888]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Algebraize the K-power quotients, with compatible maps and a uniform torsion bound.
The supplied θ is characterized by its projection equation; N and δ are constructed
jointly with σ, rather than being arbitrary objects. (Stacks, Tags 088A and 0888) -/
theorem grothendieckDevissage_secondAdicSystem_core
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (kernel (α.hom.app (op n)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
        (cokernel (α.hom.app (op n)))))
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅
        (M.obj ⋙ formalCompletionFunctor K).flip),
      (∀ e n : ℕ,
        (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n)) ∧
      (∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (kernel (δ.hom.app (op e)))) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
          (cokernel (δ.hom.app (op e))))) := by
  obtain ⟨N, δ, σ, hsquare⟩ :=
    grothendieckDevissage_secondAdicSystem_lift_data I K M hthick H α θ
  obtain ⟨t, ht, hα⟩ := htorsion
  refine ⟨N, δ, σ, hsquare, 4 * t, ?_, ?_⟩
  · omega
  · exact grothendieckDevissage_secondAdicSystem_torsion
      I K M hthick H α θ N δ σ hsquare t ht hα

end AlgebraicGeometry
