/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessQuasiFinite

/-!

# Nearby cycles of lisse extensions supported on a closed subscheme quasi-finite over the trait

Let `S = Spec k'⟦t⟧` be the strictly henselian trait, `c : D ⟶ 𝔸ⁿ_S` a closed immersion, `W` an
open of `D`, `c' : E ⟶ W` a closed immersion and `L` a lisse sheaf on `E`. If `W` lies in the
range of a closed immersion `ι : D' ⟶ D` such that `ι ≫ c ≫ q : D' ⟶ S` is locally quasi-finite
(`q` the structure map of `𝔸ⁿ_S`), then `Ψ (Rc_* j_{W!} Rc'_* L)` is bounded constructible
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_locallyQuasiFinite`).

The proof: `K = j_{W!} Rc'_* L` vanishes on the open complement of the range of `ι`, so the unit
`K ⟶ Rι_* Lι^* K` is an isomorphism and `Rc_* K ≅ R(ι ≫ c)_* Lι^* K`; conclude by the
quasi-finite case
`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_of_locallyQuasiFinite_comp`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable [IsSepClosed k'] [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
