module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Construction of the algebraized K-adic system and its comparison isomorphism.
Source: Stacks Project, Tag 088A, construction of the systems G_e.
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift-data)
The proof descends each quotient system to the closed subscheme V(K^(e+1)),
uses the assumed completion equivalence and pushes forward. -/
theorem grothendieckDevissage_secondAdicSystem_lift_data
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    (hθ : ∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H.obj ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H.obj) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H.obj ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H.obj)) :
    ∃ (N : CoherentFormalModule X K) (δ : N ⟶ (completion X K).obj H)
      (σ : N.obj ⋙ formalCompletionFunctor I ≅
        (M.obj ⋙ formalCompletionFunctor K).flip), True := by
  sorry

end AlgebraicGeometry
