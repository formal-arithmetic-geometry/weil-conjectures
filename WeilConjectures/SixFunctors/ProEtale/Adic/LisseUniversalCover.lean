/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCover
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible

/-!
# Lisse sheaves are constant on the universal profinite étale cover

Let `Y` be a connected regular Noetherian scheme and `Ỹ_y` its universal profinite étale cover
at a geometric point `y` (`AlgebraicGeometry.Scheme.UniversalCovers`). Every lisse `ℓ`-adic sheaf
`G` on `Y_proét` becomes constant on `Ỹ_y`: `G|_{Ỹ_y} ≅ ℚ̄_ℓⁿ`
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_upperStar_universalCover`).

This is the `ℚ̄_ℓ`-part of the blueprint `cor-galois-lisse-representations` in the form needed
here. The blueprint deduces it from the case of finite coefficients by passing to the
coefficient stages; in the Bhatt–Scholze model of lisse sheaves used in this project
(pro-étale locally free `ℚ̄_ℓ,Y`-modules) the passage goes through `𝒪_E`-lattices: `G` comes
from a lisse `𝒪_E`-sheaf `L` for a finite extension `E` of `ℚ_ℓ`, whose reductions `L / ϖⁿ`
are finite locally constant étale sheaves, hence finite étale covers of `Y`, which split over
`Ỹ_y`; so `L|_{Ỹ_y} = lim_n (L / ϖⁿ)|_{Ỹ_y}` is constant, and so is `G|_{Ỹ_y}`
(Bhatt–Scholze, *The pro-étale topology for schemes*, Lemma 7.4.7 and Lemma 7.4.10).
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- **Lisse sheaves are constant on the universal cover** (blueprint:
`cor-galois-lisse-representations`, the case `Λ = ℚ̄_ℓ`). On a connected regular Noetherian
scheme `Y`, the pullback of a lisse `ℓ`-adic sheaf to the universal profinite étale cover `Ỹ_y`
at a geometric point `y` is isomorphic to `ℚ̄_ℓⁿ` for some `n`. -/
theorem IsAdicLisseSheaf.exists_iso_upperStar_universalCover [IsLocallyNoetherian Y]
    [CompactSpace Y] [IsRegular Y] [ConnectedSpace Y] (U : Scheme.UniversalCovers Y Ω)
    (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {G : AdicSheaf l Y} (hG : IsAdicLisseSheaf G) :
    ∃ n : ℕ, Nonempty ((U.proj y)^*ᵃ[l].obj G ≅
      ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)) := by
  sorry

end AlgebraicGeometry.ProEtale
