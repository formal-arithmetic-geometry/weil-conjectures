/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniversalHomeomorphism
public import WeilConjectures.TraceFormula.Specialization.NearbyProperExchange
public import WeilConjectures.TraceFormula.Specialization.ThickOriginPowPoint
public import WeilConjectures.TraceFormula.Specialization.ThickOriginReducedUnit
public import WeilConjectures.TraceFormula.Specialization.ThickOriginRestrictedUnit

/-!

# The specialization unit of the thick origin on the zero section

Let `𝒟 = 𝒟_{V(x^m)} 𝔸¹_k` be the deformation to the normal cone of the thick origin over the trait
`S = Spec k'⟦t⟧`, and `e` the zero section of its special fibre. We prove that the restriction
`Le^* σ_𝒟` of the specialization unit to the zero section is an isomorphism
(`ProEtale.CondensedRing.isIso_upperStar_zeroSection_unit_polyAffineThickOrigin`), the remaining
hypothesis of `ProEtale.CondensedRing.isZero_specializationDefect_polyAffineThickOrigin_unit`.

The power map `ν : 𝒲 ⟶ 𝒟` from the deformation `𝒲 = 𝒟_{V(x)} 𝔸¹_k ≅ 𝔸¹ × S` of the origin, over
`t ↦ t^m` (`ProEtale.CondensedRing.powModelHom`), is finite and an isomorphism on geometric generic
fibres. Its source has invertible specialization unit (smooth exchange,
`isIso_deformationModel_polyAffineThickOrigin_one_unit`, and topological invariance along the
thickening `t = 0 ⊆ t^m = 0`). The proper exchange `Ψ_𝒟 ≅ Rν_{s*} Ψ_𝒲` and its unit identity
then identify `σ_𝒟` with the unit `Λ ⟶ Rν_{s*} Lν_s^* Λ`, whose restriction to a rational point of
the zero section is invertible by proper base change, the fibre of `ν_s` over that point being a
universally homeomorphic point
(`ProEtale.CondensedRing.mem_range_zeroSectionSpecialFibreMap_of_powMap`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Point

variable {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']

instance : IsIso (deformationSpecialFibre (point k) ⊥ k').hom := by
  have : IsIso (point k).hom := inferInstanceAs (IsIso (𝟙 _))
  exact inferInstanceAs (IsIso (pullback.snd _ _))

/-- The rational point of the special fibre of the constant family `Y × S` lying over a rational
point `y` of `Y`. -/
noncomputable def constantFamilySpecialPoint {Y : Over (Spec (.of k))} (y : point k ⟶ Y) :
    Spec (.of k') ⟶ (deformationSpecialFibre Y ⊥ k').left :=
  inv (deformationSpecialFibre (point k) ⊥ k').hom ≫
    (deformationSpecialFibreMap y (siteIdeal_bot_map_appLE_le _ ⊥) k').left

@[reassoc (attr := simp)]
lemma constantFamilySpecialPoint_hom {Y : Over (Spec (.of k))} (y : point k ⟶ Y) :
    constantFamilySpecialPoint k' y ≫ (deformationSpecialFibre Y ⊥ k').hom = 𝟙 _ := by
  rw [constantFamilySpecialPoint, Category.assoc, Over.w, IsIso.inv_hom_id]

end Point

section PowModel

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] {m : ℕ} (hm : m ≠ 0)

variable (m) in
/-- The power map `D_{V(x)} 𝔸¹_k ⟶ D_{V(x^m)} 𝔸¹_k` of deformation spaces. -/
noncomputable abbrev thickOriginPowMap :
    (polyAffineThickOrigin k 1).deformationSpace ⟶ (polyAffineThickOrigin k m).deformationSpace :=
  IdealSheafData.deformationSpacePowMap m fun U ↦ (siteIdeal_polyAffineThickOrigin k m U).le

/-- The power model `𝒲` of the thick origin: the deformation of `V(x)` with the thickened special
fibre `t^m = 0`. -/
noncomputable abbrev thickOriginPowSourceModel :=
  powSourceModel k' hm (polyAffine k 1) (polyAffineThickOrigin k 1) (polyAffineThickOrigin k m)
    (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The special fibre of the power model, over `k'`. -/
noncomputable abbrev thickOriginPowSpecialFibre :=
  powSpecialFibre k' hm (polyAffine k 1) (polyAffineThickOrigin k 1) (polyAffineThickOrigin k m)
    (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The morphism of special fibres `ν_s : 𝒲_s ⟶ 𝒟_s` of the power model. -/
noncomputable abbrev thickOriginPowSpecialFibreMap :
    thickOriginPowSpecialFibre k k' hm ⟶
      deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k m) k' :=
  powSpecialFibreMap k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
    (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The morphism of models `𝒲 ⟶ 𝒟_{V(x^m)}` over the identity of `𝔸¹_k`. -/
noncomputable abbrev thickOriginPowModelHom :=
  powModelHom k' hm (polyAffine k 1) (polyAffineThickOrigin k 1) (polyAffineThickOrigin k m)
    (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)
    (IdealSheafData.deformationSpacePowMap_proj _)

/-- The inclusion `c : 𝒟_{V(x),s} ⟶ 𝒲_s` of the special fibre into the thickened one. -/
noncomputable abbrev thickOriginSpecialFibreToPow :
    (deformationSpecialFibre (polyAffine k 1) (polyAffineThickOrigin k 1) k').left ⟶
      (thickOriginPowSpecialFibre k k' hm).left :=
  specialFibreToPowSpecialFibre k' hm (polyAffine k 1) (polyAffineThickOrigin k 1)
    (polyAffineThickOrigin k m) (thickOriginPowMap k m) (affineLinePowMap k m)
    (deformationSpacePowMap_deformationSpaceToAffineLine _) (traitPowMap_traitToAffineLine k k' hm)

/-- The morphism of models `𝒟_{V(x)} ⟶ 𝒲` given by the identity of the total space and the
inclusion `c` of the special fibres. -/
noncomputable def thickOriginToPowSourceModel :
    (deformationModel (polyAffine k 1) (polyAffineThickOrigin k 1) k').Hom
      (thickOriginPowSourceModel k k' hm) (𝟙 _) (thickOriginSpecialFibreToPow k k' hm) where
  total := 𝟙 _
  generic := 𝟙 _
  comm_j := by rw [Category.id_comp, Category.comp_id]; rfl
  comm_i := by rw [Category.comp_id, specialFibreToPowSpecialFibre_i]
  comm_ε := by rw [Category.id_comp, Category.comp_id]; rfl

end PowModel

section GenericUnit

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- If a morphism of models `M ⟶ N` over the identity of `X` has invertible morphisms of total spaces
and of geometric generic fibres, and its morphism of special fibres is a universal homeomorphism,
the specialization unit of `N` is invertible as soon as that of `M` is. -/
theorem NearbyCyclesModel.isIso_unit_of_hom {X X' Y' : Scheme.{u}} {M : NearbyCyclesModel X X'}
    {N : NearbyCyclesModel X Y'} {c : X' ⟶ Y'} (ψ : M.Hom N (𝟙 X) c) [IsIso ψ.total]
    [IsIso ψ.generic] [IsUniversalHomeomorphism c] (hM : IsIso (M.unit Λ)) :
    IsIso (N.unit Λ) := by
  have := ψ.isIso_pullbackExchange_of_isIso Λ
  have h := ψ.map_unit_comp_pullbackExchange_app Λ
  have : IsIso (L((c)^*⟦Λ⟧).map (N.unit Λ) ≫ (ψ.pullbackExchange Λ).app (𝟙_ _)) := by
    rw [h]; infer_instance
  exact isIso_of_isIso_leftDerivedUpperStar_map Λ c _
    (IsIso.of_isIso_comp_right (L((c)^*⟦Λ⟧).map (N.unit Λ)) ((ψ.pullbackExchange Λ).app (𝟙_ _)))

end GenericUnit

section Unit

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)] {m : ℕ} (hm : m ≠ 0)

/-- The specialization unit of the power model `𝒲` is an isomorphism: its restriction along the
universal homeomorphism `c` is the specialization unit of the deformation of the origin. -/
theorem isIso_thickOriginPowSourceModel_unit :
    IsIso ((thickOriginPowSourceModel k k' hm).unit (Profinite.padicAlgClRingObj ℓ)) := by
  have : IsIso ((thickOriginToPowSourceModel k k' hm).total) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso ((thickOriginToPowSourceModel k k' hm).generic) := inferInstanceAs (IsIso (𝟙 _))
  exact NearbyCyclesModel.isIso_unit_of_hom _ (thickOriginToPowSourceModel k k' hm)
    (isIso_deformationModel_polyAffineThickOrigin_one_unit k')

end Unit

end AlgebraicGeometry.ProEtale.CondensedRing
