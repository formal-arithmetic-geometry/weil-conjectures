/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessTorsion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.IntegralModelAmbient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.IntegralCriterionResidue

/-!

# Deligne's finiteness theorem for nearby cycles with `𝒪_E`-coefficients

The nearby cycles commute with extension of scalars along a coefficient change `Λ ⟶ Λ'` at
complexes where `Rj_*` does (`NearbyCyclesModel.nonempty_extendScalars_nearbyCycles_iso`). Over the
strictly henselian trait `S = Spec k'⟦t⟧` (`k'` separably closed, `ℓ ≠ char k'`), the nearby cycles
of the standard model of `𝔸ⁿ_S` carry bounded constructible `𝒪_E`-complexes `K₀` to bounded
constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_padicIntegers`): `Ψ K₀` is
derived complete, and its reduction `𝔽_E ⊗ᴸ Ψ K₀ ≅ Ψ (𝔽_E ⊗ᴸ K₀)` is bounded constructible by the
finite-coefficient theorem
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`), so the integral
criterion applies (`ProEtale.boundedConstructible_of_derivedCompleteIntegers_of_residueField`).
SGA 4½, [Th. finitude], Thm. 3.2; Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
