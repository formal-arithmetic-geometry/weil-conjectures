/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.UnitSections

/-!
# Modules supported on a closed subscheme

A coherent module `𝒦` on a noetherian scheme `Y` vanishing outside the image of a closed
immersion `i : T ⟶ Y` has a finite filtration `𝒦 = K₀ ⊇ K₁ ⊇ ⋯ ⊇ K_N = 0` with
`K_k / K_{k+1} ≅ i_* i^* K_k`, where `K_{k+1}` is the kernel of the unit `K_k ⟶ i_* i^* K_k`.
Hence finiteness of cohomology for coherent modules on `T` implies it for `𝒦`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

/-- **Dévissage along a closed subscheme.** Let `𝒦` be a coherent module on the noetherian
scheme `Y` which vanishes on an open `W` whose complement lies in the image of the closed
immersion `i : T ⟶ Y`. If all coherent modules on `T` have finite cohomology over `A`, so
does `𝒦`. -/
theorem finiteH_of_isZero_restrict [IsNoetherianRing A] {Y T : Scheme.{u}} [IsNoetherian Y]
    (p : Y ⟶ Spec (.of A)) (i : T ⟶ Y) [IsClosedImmersion i] (W : Y.Opens)
    (hW : (W : Set Y)ᶜ ⊆ Set.range i.base) (𝒦 : Y.Modules) [𝒦.IsQuasicoherent]
    [𝒦.IsFinitePresentation] (h𝒦 : IsZero (𝒦.restrict W.ι))
    (hT : ∀ (𝒢 : T.Modules) [𝒢.IsQuasicoherent] [𝒢.IsFinitePresentation], FiniteH (i ≫ p) 𝒢) :
    FiniteH p 𝒦 :=
  sorry

end AlgebraicGeometry.Scheme.Modules
