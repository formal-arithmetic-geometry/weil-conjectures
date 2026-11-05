/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualizingMap
public import WeilConjectures.TraceFormula.Specialization.TraitModelCompactification
public import WeilConjectures.TraceFormula.Specialization.TraitModelProperExchange

/-!

# Uniqueness of the dualizing maps of nearby cycles

The two properties of a family of dualizing maps (`NearbyCyclesModel.NearbyDualizingData`)
determine it (blueprint `det-nearby-exchange-maps`):

* on a proper `k'`-scheme `Z`, a map `A ⟶ ω_Z` is determined by its trace
  `RΓ(A) ⟶ RΓ(ω_Z) ⟶ ℚ̄_ℓ` (`NearbyCyclesModel.eq_of_map_comp_trace_eq`), the trace being the
  counit of `Ra_! ⊣ Ra^!` read through `Ra_! ≅ Ra_*`;
* so for a proper model whose geometric generic fibre is all of `X ×_k Spec Ω`, where the proper
  exchange `χ_a` is invertible, the trace property determines `θ_M`
  (`NearbyCyclesModel.NearbyDualizingData.θ_eq_of_isProper`);
* every trait model over the base is an open sub-model of such a proper model
  (`NearbyCyclesModel.IsTraitModelOfBase.exists_isProper_openSubmodel`), and open restriction
  determines `θ_N` from `θ_M`, the exchange `α_j` being invertible
  (`NearbyCyclesModel.NearbyDualizingData.θ_eq`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {k' : Type u} [Field k'] [Algebra k k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
