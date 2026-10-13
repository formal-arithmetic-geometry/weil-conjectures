module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Compatibility of the algebraized system with the original comparison map.
Source: Stacks Project, Tag 088A, lifting the comparison maps by full faithfulness.
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift-compatibility)
The statement records the final faithfulness argument after the algebraizations have
been chosen; its proof is the categorical lifting step of the construction. -/
theorem grothendieckDevissage_secondAdicSystem_lift_compatibility
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    {N : CoherentFormalModule X K} (δ : N ⟶ (completion X K).obj H)
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip) :
    ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n) := by
  sorry

end AlgebraicGeometry
