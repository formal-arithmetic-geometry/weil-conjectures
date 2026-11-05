/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityExchange

/-!

# Nearby duality and global sections: the concrete inputs

For a trait model `M` over the base with proper `X`, `X'` and proper total space, the global
sections `RΓ(X', δ_{M,K})` of the duality map are compared with the duality map of the trait by
the abstract identity `CategoryTheory.Verdier.isIso_map_nearbyDualityMap_of_proper` (blueprint
`det-tf-nearby-duality-proper` (1), (3)), applied to `G = Ra_*`, `G' = Ra'_*` and the proper
exchange `χ_a`. Its concrete inputs, proved in
`TraceFormula.Specialization.NearbyDualityLaxMonoidal` and
`TraceFormula.Specialization.NearbyDualityExchange`, are:

* the lax monoidal structure of `Rf_*` on bounded constructible complexes, the right adjoint of
  the monoidal functor `Lf^*` (`ProEtale.CondensedRing.boundedConstructibleLowerStarLaxMonoidal`);
* the compatibility of the pushforward exchange `χ_f` with the lax tensor maps
  (`NearbyCyclesModel.Hom.boundedConstructiblePushforwardExchange_tensor`), from the monoidality
  of the pullback exchange through the abstract computation
  `ProEtale.CondensedRing.kunnethMap_comp_pushforwardExchange_aux` of the Künneth map, specialised
  to the diagonal;
* **global Verdier duality**: for a proper `k`-scheme `Z`, the duality map of `(Ra_*, μ, tr_Z)`
  is the Verdier exchange morphism `Ra_* RHom(K, ω_Z) ≅ RHom(Ra_! K, ℚ̄_ℓ)` read through
  `Ra_! ≅ Ra_*` (`CategoryTheory.Verdier.nearbyDualityMap_comp_pre_eq_exchange`), hence is an
  isomorphism (`ProEtale.CondensedRing.isIso_nearbyDualityMap_lowerStar_trace`). The
  identification uses that the exceptional projection morphism of a proper morphism is the
  projection morphism of `Lf^* ⊣ Rf_!`
  (`ProEtale.CondensedRing.upperStar_map_exceptionalProjection_comp_counit`, blueprint
  `prop-sf-pf-coherence`).

With these, `RΓ(X', δ_{M,K})` is an isomorphism as soon as the proper exchange `χ_a` is invertible
and the duality map of the trait is invertible at `Ra_* K`
(`NearbyCyclesModel.isIso_lowerStar_nearbyDualityMap_of_isIso`).

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

/-! ### The lax monoidal structure of nearby cycles -/

namespace NearbyCyclesModel

section LaxMonoidal

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

end LaxMonoidal

section Trait

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k : Type u) [Field k] (k' : Type u) [Field k'] [IsSepClosed k'] [Algebra k k']

end Trait

section BoundedConstructible

variable {ℓ : ℕ} [Fact ℓ.Prime] {k k' : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left}

set_option hygiene false in
/-- The condensed field `ℚ̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj ℓ

end BoundedConstructible

end NearbyCyclesModel

/-! ### Global sections of the duality map -/

namespace NearbyCyclesModel

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {k' : Type u} [Field k'] [Fact (ringChar k').Prime]
  [Fact (ringChar k' ≠ ℓ)] [IsSepClosed k'] [Algebra k k']
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] {M : NearbyCyclesModel X.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
