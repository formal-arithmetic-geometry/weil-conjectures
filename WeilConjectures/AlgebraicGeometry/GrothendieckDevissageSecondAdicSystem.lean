/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemCore
import WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemComparison

/-! # The second adic system in Grothendieck devissage

## References

* [Stacks Project, Tag 088A]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Construct the K-adic system by algebraizing the K-power quotients of an I-adic system.
The isomorphism sigma records compatibility in both indices, not just on individual terms.
The isomorphism theta is the canonical interchange of the two quotient operations:
its equation with the two quotient projections specifies it uniquely. (Stacks, Tag 088A) -/
theorem grothendieckDevissage_secondAdicSystem
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
        (cokernel (α.hom.app (op n))))) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅ (M.obj ⋙ formalCompletionFunctor K).flip)
      (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
        (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip),
      (∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H.obj ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H.obj ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj)) ∧
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
  obtain ⟨θ, hθ⟩ := grothendieckDevissage_secondAdicSystem_comparison I K H.obj
  obtain ⟨N, δ, σ, hsquare, htorsionδ⟩ :=
    grothendieckDevissage_secondAdicSystem_core I K M hthick H α htorsion θ
  exact ⟨N, δ, σ, θ, hθ, hsquare, htorsionδ⟩

end AlgebraicGeometry
