/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessPadicIntegers

/-!

# Deligne's finiteness theorem for nearby cycles with `ℚ̄_ℓ`-coefficients

Over the strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the
geometric nearby cycles of the standard model of `𝔸ⁿ_S` carry bounded constructible
`ℚ̄_ℓ`-complexes to bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_integral`; SGA 4½,
[Th. finitude], Thm. 3.2, for `ℚ̄_ℓ`-coefficients as in Bhatt–Scholze §6.8). It is deduced from the
case of the finite coefficients `𝔽_E = 𝒪_E/ϖ`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`):

* a bounded constructible `ℚ̄_ℓ`-complex `B` has an integral model: `B ≅ ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} K₀`
  for a derived complete bounded constructible `𝒪_E`-complex `K₀`
  (`ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`);
* the nearby cycles commute with these extensions of scalars on bounded below complexes
  (`NearbyCyclesModel.nonempty_extendScalars_nearbyCycles_iso`, from the pullbacks and from
  `Rj_*`), so `Ψ B ≅ ℚ̄_ℓ ⊗ᴸ_E E ⊗ᴸ_{𝒪_E} Ψ K₀` and `𝔽_E ⊗ᴸ Ψ K₀ ≅ Ψ (𝔽_E ⊗ᴸ K₀)`;
* `Ψ K₀` is derived complete (pullbacks and pushforwards preserve derived completeness) and its
  reduction `Ψ (𝔽_E ⊗ᴸ K₀)` is bounded constructible by the finite-coefficient theorem, so `Ψ K₀`
  is bounded constructible by the integral criterion
  (`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`), and so is `Ψ B`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
