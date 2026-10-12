/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# Sections of the twisting sheaves not vanishing at a point

For a morphism `e : X ⟶ ℙ(N; S)`, a point `x` of `X` and `n : ℕ`, there is a global section of
`e^* 𝒪(n)` which does not vanish at `x`: the pullback of `Tᵢⁿ` for a coordinate `Tᵢ` not
vanishing at `e x`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

/-- For `e : X ⟶ ℙ(N; S)`, `x : X` and `n : ℕ` there is a section `𝒪_X ⟶ e^* 𝒪(n)` not vanishing
at `x`. -/
theorem exists_twistRestrict_section {N : Type u} {S X : Scheme.{u}} (e : X ⟶ ℙ(N; S)) (x : X)
    (n : ℕ) : ∃ s : 𝟙_ X.Modules ⟶ twistRestrict e n,
      x ∈ (Hom.zeroLocus s).support.compl :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
