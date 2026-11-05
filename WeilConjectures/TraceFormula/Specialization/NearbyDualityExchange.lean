/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityLaxMonoidal

/-!

# Nearby duality and global sections: the pushforward exchange

Concrete inputs for `TraceFormula.Specialization.NearbyDualityGlobal`:

* the compatibility of the pushforward exchange `χ_f` with the lax tensor maps
  (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`);
* **global Verdier duality** (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- `Dᵇc` is monoidal through `ObjectProperty.fullMonoidalSubcategory` everywhere, so that the
-- monoidal structures of concrete statements and of instantiated abstract ones agree syntactically.
attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

/-! ### The pushforward exchange and the lax tensor maps -/

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {M : NearbyCyclesModel X.left X'.left} {N : NearbyCyclesModel Y.left Y'.left}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f.left f'.left)
  (hM : M.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ)) (hN :
      N.PreservesBoundedConstructible (Profinite.padicAlgClRingObj ℓ))

end NearbyCyclesModel

/-! ### Global Verdier duality -/

section Global

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (Z : Over (Spec (.of k))) [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [IsProper (toPoint Z).left]

/-- **Global Verdier duality** (blueprint `det-tf-nearby-duality-proper` (3), "global Verdier
duality"): for a proper `k`-scheme `Z` with structure morphism `a`, the duality map
`Ra_* D_Z K ⟶ RHom(Ra_* K, ℚ̄_ℓ)` of `(Ra_*, μ, tr_Z)` (`μ` the lax structure
`boundedConstructibleLowerStarLaxMonoidal`, `tr_Z` the trace `NearbyCyclesModel.trace`) is an
isomorphism: read through `Ra_! ≅ Ra_*` it is the Verdier exchange morphism
(`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`), an isomorphism by
`ProEtale.CondensedRing.isIso_verdierExchange`. -/
theorem isIso_nearbyDualityMap_lowerStar_trace (K : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (Verdier.nearbyDualityMap
      (letI := boundedConstructibleLowerStarLaxMonoidal ℓ
        (toPoint Z);
        Functor.LaxMonoidal.μ (boundedConstructibleLowerStar ℓ (toPoint Z)))
      (NearbyCyclesModel.trace ℓ Z) K) := by
  have e := Verdier.nearbyDualityMap_comp_pre_eq_exchange
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint Z))
    (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z))
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z))
    (boundedConstructibleExceptionalProjection ℓ (toPoint Z))
    (fun T B ↦ upperStar_map_exceptionalProjection_comp_counit ℓ (toPoint Z) T B) K (𝟙_ _)
  have h₁ : IsIso (Verdier.exchange
      (boundedConstructibleUpperStarLowerStarAdjunction ℓ (toPoint Z))
      (boundedConstructibleUpperShriekAdjunction ℓ (toPoint Z))
      (boundedConstructibleExceptionalProjection ℓ (toPoint Z)) K (𝟙_ _)) :=
    isIso_verdierExchange ℓ (toPoint Z) K (𝟙_ _)
  have h₂ := isIso_pre_app
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ (toPoint Z)).hom.app K) (𝟙_ _)
  rw [← e] at h₁
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₂ h₁

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
