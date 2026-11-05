/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessFinite

/-!

# Nearby cycles of complexes supported on a closed subscheme quasi-finite over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait (`k'` separably closed, `ℓ ≠ char k'`) and
`c : D ⟶ 𝔸ⁿ_S` a closed immersion such that `p = c ≫ q : D ⟶ S` is locally quasi-finite, `q` being
the structure map of `𝔸ⁿ_S`. For every bounded constructible `ℚ̄_ℓ`-complex `K` on `D`, the
geometric nearby cycles of `Rc_* K` are bounded constructible on the special fibre `𝔸ⁿ_s`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_locallyQuasiFinite_comp`).
This generalizes the finite case
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_isFinite_comp`.

The proof:
* for a scheme `p̄ : T ⟶ S` finite over the trait, the geometric nearby cycles of its standard
  model preserve bounded constructible complexes
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_traitStdModel_of_isFinite`): by
  the proper exchange along `p̄`, `Rp̄_{s*} Ψ_T B ≅ Ψ_S (Rp̄_* B)`, and `T_s` is finite over the
  separably closed point `Spec k'`;
* by Zariski's main theorem
  (`AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite`), `p`
  factors as an open immersion `j : D ⟶ T` followed by a finite `p̄ : T ⟶ S`. Nearby cycles
  commute with the open immersion `j`
  (`NearbyCyclesModel.Hom.isIso_pullbackExchange_of_isOpenImmersion`), so
  `Ψ_D K ≅ Ψ_D (Lj^* j_! K) ≅ Lj_s^* Ψ_T (j_! K)` is bounded constructible
  (`NearbyCyclesModel.boundedConstructible_geometricNearbyCycles_traitStdModel_of_isOpenImmersion`);
* by the proper exchange along `c`, `Ψ_{𝔸ⁿ} (Rc_* K) ≅ Rc_{s*} Ψ_D K`.

The proper exchange is `sorry`ed upstream
(`WeilConjectures.TraceFormula.Specialization.NearbyProperExchange`), as is the finiteness of
proper direct images.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
