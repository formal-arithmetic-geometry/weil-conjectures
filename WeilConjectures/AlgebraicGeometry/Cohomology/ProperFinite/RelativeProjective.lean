/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Basic

/-!
# Proper morphisms with a projective source

Let `p : Y ⟶ Spec A` be proper, `A` noetherian, and `π : Y' ⟶ Y` proper with a closed immersion
`e : Y' ⟶ ℙ(N; Spec A)` over `Spec A`. Over every affine open `V` of `Y`, the preimage
`π ⁻¹ᵁ V` is a closed subscheme of `ℙ(N; Spec Γ(Y, V))`. Hence `π_*` preserves coherence, and
relative Serre vanishing holds: `R^q π_* (G ⊗ e^* 𝒪(n)) = 0` for `q > 0` and `n ≫ 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] {Y Y' : Scheme.{u}} (p : Y ⟶ Spec (.of A)) (π : Y' ⟶ Y)
  {N : Type u} (e : Y' ⟶ ℙ(N; Spec (.of A)))

/-- Over an affine open `V` of `Y`, `π ⁻¹ᵁ V` is a closed subscheme of `ℙ(N; Spec Γ(Y, V))`,
compatibly with the twisting sheaves. -/
theorem exists_isClosedImmersion_preimage [IsProper p] [IsProper π] [IsClosedImmersion e]
    (he : e ≫ ℙ(N; Spec (.of A)) ↘ Spec (.of A) = π ≫ p) {V : Y.Opens} (hV : IsAffineOpen V) :
    ∃ eV : (π ⁻¹ᵁ V).toScheme ⟶ ℙ(N; Spec Γ(Y, V)), IsClosedImmersion eV ∧
      eV ≫ ℙ(N; Spec Γ(Y, V)) ↘ Spec Γ(Y, V) = (π ∣_ V) ≫ hV.isoSpec.hom ∧
      ∀ n : ℤ, Nonempty (ProjectiveSpace.twistRestrict eV n ≅
        (pullback (π ⁻¹ᵁ V).ι).obj (ProjectiveSpace.twistRestrict e n)) :=
  sorry

/-- `π_*` preserves coherence. -/
theorem isFinitePresentation_pushforward_of_projective [IsNoetherianRing A] [Finite N]
    [IsProper p] [IsProper π] [IsClosedImmersion e]
    (he : e ≫ ℙ(N; Spec (.of A)) ↘ Spec (.of A) = π ≫ p) (G : Y'.Modules) [G.IsQuasicoherent]
    [G.IsFinitePresentation] : ((pushforward π).obj G).IsFinitePresentation :=
  sorry

/-- **Relative Serre vanishing.** For coherent `G` on `Y'`, `R^q π_* (G ⊗ e^* 𝒪(n)) = 0` for all
`q > 0` and `n ≫ 0`. -/
theorem exists_isZero_higherDirectImage_tensorObj_twistRestrict [IsNoetherianRing A] [Finite N]
    [IsProper p] [IsProper π] [IsClosedImmersion e]
    (he : e ≫ ℙ(N; Spec (.of A)) ↘ Spec (.of A) = π ≫ p) [HasInjectiveResolutions Y'.Modules]
    (G : Y'.Modules) [G.IsQuasicoherent] [G.IsFinitePresentation] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q : ℕ,
      IsZero ((higherDirectImage π (q + 1)).obj (G ⊗ ProjectiveSpace.twistRestrict e n)) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
