module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Interchanging two ideal-power quotients

Source: Stacks Project, Tag 088A, the quotient by I^n + K^e
(blueprint: lem-weil-pbc-devissage-second-adic-system-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical quotient interchange, natural in both positive indices.
Source: Stacks Project, Tag 088A, the quotient by I^n + K^e
(blueprint: lem-weil-pbc-devissage-second-adic-system-comparison).

Proof: a map out of (H/K^e H)/I^n is precisely a map out of H killing both
K^e H and I^n H, by the two cokernel universal properties. Tensoring by an
ideal module preserves epimorphisms, so vanishing of its product can be checked
after the first quotient projection. The quotient in
the other order has the same property. Factor its composite projection through
the first quotient, and conversely. Both composites are identities: precompose
with the composite quotient projection, which is epi, and use the defining
factorization equations. These equations also give the displayed identity.
For either index transition, precomposing the naturality square with the
projection from H gives the same quotient projection on both paths. Epimorphism
cancellation proves the square, so the component isomorphisms assemble to θ.
-/
theorem grothendieckDevissage_secondAdicSystem_comparison
    {X : Scheme.{u}} (I K : X.IdealSheafData) (H : X.Modules) :
    ∃ (θ : formalCompletionSystem K H ⋙ formalCompletionFunctor I ≅
        (formalCompletionSystem I H ⋙ formalCompletionFunctor K).flip),
      ∀ e n : ℕ,
        formalModuleQuotientπ K (e + 1) H ≫
          formalModuleQuotientπ I (n + 1) (formalModuleQuotient K (e + 1) H) ≫
          (θ.hom.app (op e)).app (op n) =
        formalModuleQuotientπ I (n + 1) H ≫
          formalModuleQuotientπ K (e + 1) (formalModuleQuotient I (n + 1) H) := by
  sorry

end AlgebraicGeometry
