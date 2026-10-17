/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseUniversalCover

/-!
# Existence of the monodromy of lisse sheaves

On a connected regular Noetherian scheme `Y`, the universal profinite étale covers exist
(`AlgebraicGeometry.Scheme.nonempty_universalCovers`) and lisse sheaves become free on them
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_iso_upperStar_universalCover`), so they
define a monodromy of lisse sheaves (`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy`),
which is an equivalence at every base point
(`AlgebraicGeometry.Scheme.UniversalCovers.lisseMonodromy_isEquivalenceAt`). This is
`AlgebraicGeometry.ProEtale.exists_lisseMonodromy`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (Ω : Type u) [Field Ω]

/-- **Lisse `ℚ̄_ℓ`-sheaves and continuous representations** (blueprint:
`cor-galois-lisse-representations`, the case `Λ = ℚ̄_ℓ`). On a connected regular Noetherian
scheme `Y` (hence geometrically unibranch), the stalks of lisse `ℓ`-adic sheaves carry a
monodromy along paths of fibre functors, compatible with reparametrisation, pullback, global
sections and duals, which at every base point `t` identifies lisse sheaves with continuous
finite-dimensional `ℚ̄_ℓ`-representations of `π₁(Y, t)`.

It is constructed from the universal profinite étale covers `Ỹ_y` of `Y`: the stalk of a lisse
sheaf at `y` is its space of sections over `Ỹ_y`, on which it is constant, and paths act through
the transport of the universal covers. -/
theorem exists_lisseMonodromy [IsLocallyNoetherian Y] [CompactSpace Y] [IsRegular Y]
    [ConnectedSpace Y] :
    ∃ M : LisseMonodromy l Y Ω, ∀ t, M.IsEquivalenceAt t := by
  obtain ⟨U⟩ := Scheme.nonempty_universalCovers Y Ω
  have hU (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y) :
      ∃ n : ℕ, Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅
        ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)) :=
    IsAdicLisseSheaf.exists_iso_upperStar_universalCover U y G.property
  exact ⟨U.lisseMonodromy hU, U.lisseMonodromy_isEquivalenceAt hU⟩

end AlgebraicGeometry.ProEtale
