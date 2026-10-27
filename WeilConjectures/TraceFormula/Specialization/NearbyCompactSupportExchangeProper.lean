/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCompactSupportExchange

/-!

# The compact-support exchange of a proper trait model

For a trait model `N` over the base of a proper `k`-scheme `Y` with proper special fibre, the
compact-support exchange `ν_a : Ra'_! Ψ_N ⟶ Ψ_S Ra_!` of a compactification is the inverse of the
proper exchange `χ_a` under `Ra_! ≅ Ra_*` and `Ra'_! ≅ Ra'_*`
(`Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [IsSepClosed k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [Algebra k k']

namespace IsTraitModelOfBase

variable {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] {Y' : Over (Spec (.of k'))} [LocallyOfFiniteType Y'.hom]
  [QuasiCompact Y'.hom] [IsSeparated Y'.hom] {N : NearbyCyclesModel Y.left Y'.left}
  {q : N.total ⟶ trait k'} {g : N.generic ⟶ Spec (.of (traitGenericField k'))}

/-- **The compact-support exchange of a proper model is the inverse of the proper exchange**: for
a trait model `N` of a proper `Y` with proper special fibre and a compactification `C`, the
exchange `ν_C` followed by `Ra_! ≅ Ra_*` and the proper exchange `χ_a` is `Ra'_! ≅ Ra'_*`. -/
theorem Compactification.compactSupportExchange_app_comp_map_comp_pushforwardExchange_app
    [IsProper (toPoint Y).left] [IsProper (toPoint Y').left] {h : N.IsTraitModelOfBase k q g}
    (C : h.Compactification) (K : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (C.compactSupportExchange ℓ).app K ≫
        (traitSpecialization k k' (ℓ := ℓ)).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y)).hom.app K) ≫
        (h.pushforwardExchange ℓ).app K =
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Y')).hom.app
        ((boundedConstructibleNearbyCycles (h.preservesBoundedConstructible ℓ)).obj K) :=
  sorry

end IsTraitModelOfBase

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
