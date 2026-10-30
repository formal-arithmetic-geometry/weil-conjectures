/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbySliceInputs
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeSplitMono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.IntegralModelAmbient

/-!
# (M2) from torsion retractions

The main result is
`isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_unique_retractions`.

This file proves the averaging splitting (M2) of the slice step of Deligne's finiteness theorem
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom`, SGA 4½,
[Th. finitude], Lemme 3.4) from its torsion input:
the base change morphism of `Rj_*` along the change of generic fibres, restricted to the special
fibre, has unique torsion retractions (`ProEtale.CondensedRing.HasUniqueTorsionRetractions`; the
retractions invariant under the pro-`p` group `P`), for every integral model.

All the schemes involved are affine, `B` has an integral model on the noetherian scheme
`𝔸ⁿ⁺¹_S` (`ProEtale.CondensedRing.exists_derivedCompleteIntegers_iso_integralModel`), and the
retractions lift to `𝒪_E` and pass to `ℚ̄_ℓ`
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_unique_retractions`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme PadicAlgCl

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

set_option maxHeartbeats 1000000 in
-- the torsion hypotheses are elaborated against the large types of the slice models
/-- **(M2) from its torsion input** (SGA 4½, [Th. finitude], Lemme 3.4): the pullback exchange of
the change of generic fibres `toCartesian` of the slice `σ` over the generic slice trait is a split
monomorphism at a bounded constructible `B`, provided that for every derived complete
`𝒪_E`-complex `K₀` (for instance an integral model of `B`), the restricted base change
morphism has unique torsion retractions (`ProEtale.CondensedRing.HasUniqueTorsionRetractions`). -/
theorem isSplitMono_pullbackExchange_app_toCartesian_genericSliceTraitHom_of_unique_retractions
    (D : GenericSliceTrait k') (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B)
    (htors : ∀ (E : FiniteIntermediateField ℓ)
      (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
        (affineSpaceModel k' (n + 1)).total) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
          (affineSpaceModel k' (n + 1)).total))),
      derivedCompleteIntegers ℓ E (affineSpaceModel k' (n + 1)).total K₀ →
      HasUniqueTorsionRetractions ℓ E
        ((L(((genericSliceTraitModel D n i).i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map
          ((Adjunction.exchangeRight
            (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
              (genericSliceTraitHom D n i).cartesianModel.j)
            (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1)
              (genericSliceTraitModel D n i).j)
            (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1)
              (genericSliceTraitHom D n i).toCartesian.commSq_j)).app
            ((L(((genericSliceTraitHom D n i).cartesianModel.ε)^*⟦Profinite.padicIntegersRingObj
              ℓ E.1⟧)).obj K₀)))) :
    IsSplitMono (((genericSliceTraitHom D n i).toCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  have : IsNoetherian (affineSpaceModel k' (n + 1)).total :=
    (isTraitModel_affineSpaceModel (k' := k') (n + 1)).isNoetherian_total
  -- all the schemes of the slice are affine
  have : IsAffine (affineSpaceModel k' (n + 1)).total :=
    inferInstanceAs (IsAffine 𝔸(ULift.{u} (Fin (n + 1)); trait k'))
  have : IsAffine (affineSpaceModel k' (n + 1)).geometric.total :=
    inferInstanceAs (IsAffine (affineSpaceModel k' (n + 1)).total)
  have : IsAffine (affineSpaceModel k' (n + 1)).geometric.generic :=
    inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine (genericSliceTraitModel D n i).total := inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine (genericSliceTraitModel D n i).generic :=
    inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine
      (pullback (genericSliceTraitStructure D n i) (Spec.map (CommRingCat.ofHom D.b))) :=
    inferInstance
  have : IsAffine (genericSliceTraitHom D n i).cartesianModel.generic :=
    inferInstanceAs (IsAffine (pullback _ _))
  have : IsAffine (genericSliceTraitHom D n i).cartesianModel.total :=
    inferInstanceAs (IsAffine (genericSliceTraitModel D n i).total)
  obtain ⟨E, K₀, n₀, hK₀, hn₀, ⟨e⟩⟩ := exists_derivedCompleteIntegers_iso_integralModel ℓ hB
  exact Hom.isSplitMono_pullbackExchange_app_of_unique_retractions
    (genericSliceTraitHom D n i).toCartesian E K₀ hK₀ n₀ e (htors E K₀ hK₀)

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
