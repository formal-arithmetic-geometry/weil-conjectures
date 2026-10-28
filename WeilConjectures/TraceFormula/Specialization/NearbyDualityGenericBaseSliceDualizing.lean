/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyDualityGenericBaseSliceTwist

/-!

# The dualizing maps and generic slicing

The dualizing map of a trait model over a generic base restricts, along the slice exchange, to a
dualizing map of its generic slice which is the twist by `ℚ̄_ℓ(1)[2]` of the dualizing map of the
slice model (`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap`,
blueprint `det-tf-nearby-duality-slice`, "the twist (1)" and "the map `θ`"). It is deduced from
the twist of the dualizing complexes on the fibres of the coordinate
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_dualizingComplex_genericSlice_twist`, blueprint
`det-pd-generic-dualizing-twist`) and the compatibility of the dualizing maps with slicing for
any such twist identifications
(`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap_of_twist`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [-instance] monoidalCategory_boundedConstructible
  ObjectProperty.instMonoidalCategoryStructFullSubcategory

namespace NearbyCyclesModel


variable {F : Type u} [Field F] {k' : Type u} [Field k'] {X₁ : Over (Spec (.of F))}
  {X' : Over (Spec (.of k'))} {ι : Spec (.of (FractionRing (PowerSeries k'))) ⟶ Spec (.of F)}
  {M : NearbyCyclesModel X₁.left X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)]
  [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [Fact (ringChar (traitSliceField k')).Prime] [Fact (ringChar (traitSliceField k') ≠ ℓ)]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k')))).Prime]
  [Fact (ringChar (FractionRing (PowerSeries (traitSliceField k'))) ≠ ℓ)]
  (h : M.IsTraitModelOfGenericBase X₁ ι q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  [LocallyOfFiniteType (genericSliceBase (traitSliceCoord k') hb).hom]
  [QuasiCompact (genericSliceBase (traitSliceCoord k') hb).hom]
  [IsSeparated (genericSliceBase (traitSliceCoord k') hb).hom]
  [LocallyOfFiniteType (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [QuasiCompact (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]
  [IsSeparated (baseChangeSpecial b (traitSlice (traitSliceCoord k'))).hom]

namespace IsTraitModelOfGenericBase

/-- **The dualizing maps are compatible with generic slicing** (blueprint
`det-tf-nearby-duality-slice`, "the map `θ`"), for twist identifications
`τ_g : c^* ω_{X₁} ≅ ω_{X₂}(1)[2]` and `τ_s : p^* ω_{X'} ≅ ω_{𝒳''_s}(1)[2]` of the dualizing
complexes on the fibres of the coordinate. There is a dualizing map
`θ : Ψ_{M''} c^* ω_{X₁} ⟶ p^* ω_{X'}` of the generic slice model such that
* `θ` restricts `p^* θ_M` along the slice exchange: `p^* θ_M = θ ∘ α_{ω_{X₁}}`;
* the duality map for `θ` is an isomorphism wherever the duality map `δ_{M''}` of the slice
  model for the family `DK` is (through `τ_g`, `τ_s`, `θ` is the twist of `θ_{M''}`, up to an
  automorphism of the dualizing complex);
* `θ` is invariant under the automorphisms of the generic slice model which are the identity on
  its total space (inertia acts trivially on `ℚ̄_ℓ(1)`).

Unfinished. The blueprint proof embeds `𝒳` locally over `𝔸¹_S` as a closed subscheme of
`𝔸^r_{𝔸¹_S}`, identifies `θ` on the smooth model and its slice with the smooth purity
isomorphisms (`Ψ(ℚ̄_ℓ) ≅ ℚ̄_ℓ` for smooth models), which differ by `ℚ̄_ℓ(1)[2]`, and transports
along the exceptional exchange `β_i` of the closed immersion. -/
theorem exists_genericSliceDualizingMap_of_twist (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ)
    (τg : (genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁) ≅
      dualizingComplex ℓ (genericSliceBase (traitSliceCoord k') hb) ⊗
        boundedConstructibleTateTwist ℓ (genericSliceBase (traitSliceCoord k') hb) 1 2)
    (τs : (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X') ≅
      dualizingComplex ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k'))) ⊗
        boundedConstructibleTateTwist ℓ (baseChangeSpecial b (traitSlice (traitSliceCoord k')))
          1 2) :
    ∃ θ : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
        ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁)) ⟶
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X'),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) =
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫ θ ∧
        (∀ A : Dᵇc((genericSliceBase (traitSliceCoord k') hb).left)⟦
            Profinite.padicAlgClRingObj ℓ⟧,
          IsIso (nearbyDualityMapOfGenericBase ℓ DK
            (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
              h.isTraitModelOver) A) →
          IsIso (genericSliceDualityMap (traitSliceCoord k') ℓ h hb θ A)) ∧
        ∀ ψ : (genericSliceModel (traitSliceCoord k') hb).Hom
            (genericSliceModel (traitSliceCoord k') hb) (𝟙 _) (𝟙 _),
          ψ.total = 𝟙 _ → IsIso ψ.generic →
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb ψ).app _ ≫ θ = θ := by
  sorry

/-- **The dualizing maps and generic slicing** (blueprint `det-tf-nearby-duality-slice`,
"the twist (1)" and "the map `θ`"): the compatibility
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_genericSliceDualizingMap_of_twist` for the
twist identifications of
`NearbyCyclesModel.IsTraitModelOfGenericBase.exists_dualizingComplex_genericSlice_twist`. -/
theorem exists_genericSliceDualizingMap (D : NearbyDualizingDataOfGenericBase k' ℓ)
    (DK : NearbyDualizingDataOfGenericBase (traitSliceField k') ℓ) :
    ∃ θ : (genericSliceNearbyCycles (traitSliceCoord k') ℓ h hb).obj
        ((genericSliceUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X₁)) ⟶
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).obj (dualizingComplex ℓ X'),
      (sliceSpecialUpperStar (traitSliceCoord k') ℓ h hb).map (D.θ h) =
          (genericSliceExchange (traitSliceCoord k') ℓ h hb).app (dualizingComplex ℓ X₁) ≫ θ ∧
        (∀ A : Dᵇc((genericSliceBase (traitSliceCoord k') hb).left)⟦
            Profinite.padicAlgClRingObj ℓ⟧,
          IsIso (nearbyDualityMapOfGenericBase ℓ DK
            (isTraitModelOfGenericBase_genericSliceModel (traitSliceCoord k') hb
              h.isTraitModelOver) A) →
          IsIso (genericSliceDualityMap (traitSliceCoord k') ℓ h hb θ A)) ∧
        ∀ ψ : (genericSliceModel (traitSliceCoord k') hb).Hom
            (genericSliceModel (traitSliceCoord k') hb) (𝟙 _) (𝟙 _),
          ψ.total = 𝟙 _ → IsIso ψ.generic →
            (genericSliceSelfAction (traitSliceCoord k') ℓ h hb ψ).app _ ≫ θ = θ := by
  obtain ⟨⟨τg⟩, ⟨τs⟩⟩ := h.exists_dualizingComplex_genericSlice_twist ℓ hb
  exact h.exists_genericSliceDualizingMap_of_twist ℓ hb D DK τg τs

end IsTraitModelOfGenericBase

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
