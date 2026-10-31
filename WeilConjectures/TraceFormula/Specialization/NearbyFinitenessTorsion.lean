/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSliceFinite
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessGlobalFinite
public import WeilConjectures.TraceFormula.Specialization.ProjectiveSpaceModel

/-!

# Deligne's finiteness theorem for nearby cycles with finite coefficients

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic exponent `p`, and `T` a finite
discrete ring in which `p` is invertible (its exponent is then invertible in `k'`). Deligne's
finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2) for the affine spaces: the geometric nearby
cycles of the standard model of `𝔸ⁿ_S` carry bounded constructible complexes of `T̲`-modules to
bounded constructible complexes
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj_of_finite`).

The proof is Deligne's induction on `n`, for all separably closed fields `k'` at once:
* for `n = 0`, `𝔸⁰_S = S` is proper over `S` and its special fibre has no non-closed point, so
  the global step (`NearbyCyclesModel.boundedConstructible_nearbyCycles_traitStdModel_of_finite`)
  applies with no slices;
* for `n + 1`, extend `B` by zero along the chart `𝔸ⁿ⁺¹_S ⊆ ℙⁿ⁺¹_S` to `B̃`. The pullbacks of
  `Ψ_ℙ B̃` along the charts `eₐ,ₛ` are the nearby cycles `Ψ_𝔸 (eₐ^* B̃)` (open exchange), whose
  pullbacks to the coordinate generic slices `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` are retracts of the nearby
  cycles over `Spec K⟦t⟧` of complexes on `𝔸ⁿ_{K⟦t⟧}`
  (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite`), bounded
  constructible by induction. The maps `eₐ,ₛ ∘ hᵢ,ₛ` reach every non-closed point of `ℙⁿ⁺¹_{k'}`
  (`NearbyCyclesModel.exists_projectiveSpaceChartSpecial_affineSpaceSliceSpecialFibre_eq`), so the
  global step shows that `Ψ_ℙ B̃` is bounded constructible, and so is its restriction
  `Ψ_𝔸 B` to the chart.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **The slice step with finite coefficients, as a finiteness statement**: if the nearby cycles
over `Spec K⟦t⟧` (`K = k'(x)^alg`) of `𝔸ⁿ_{K⟦t⟧}` preserve bounded constructible complexes, then the
restrictions `Lhᵢ,ₛ^* Ψ C` of the nearby cycles of bounded constructible complexes `C` on `𝔸ⁿ⁺¹_S`
to the coordinate generic slices are bounded constructible: they are retracts of the nearby cycles
of `Lhᵢ^* C` (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite`). -/
theorem boundedConstructible_upperStar_nearbyCycles_affineSpaceSlice_of_finite
    {k' : Type u} [Field k'] [IsSepClosed k'] (n : ℕ) (i : Fin (n + 1)) {p : ℕ} [Fact p.Prime]
    (hp : ∀ m : ℕ, (m : k') = 0 → p ∣ m) (hpT : IsUnit (p : T))
    (ih : ∀ {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (affineSpaceModel (traitSliceField k') n).total) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj T)
          (affineSpaceModel (traitSliceField k') n).total))},
      boundedConstructible _ C →
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
        (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
          trait (traitSliceField k'))).left)
        (((affineSpaceModel (traitSliceField k') n).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj C))
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.continuousMapRingObj T)
        (affineSpaceModel k' (n + 1)).total))}
    (hC : boundedConstructible _ C) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
        trait (traitSliceField k'))).left)
      ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.continuousMapRingObj T⟧)).obj
        (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
          (Profinite.continuousMapRingObj T)).obj C)) := by
  have hs := isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_finite T n i hp hpT
    ((boundedConstructible_iff_of_finite T C).1 hC).plusEtaleOrigin
  exact boundedConstructible_of_retract_of_finite T
    ⟨_, retraction (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.continuousMapRingObj T)).app C), IsSplitMono.id _⟩
    (ih (boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ _ C hC))

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
