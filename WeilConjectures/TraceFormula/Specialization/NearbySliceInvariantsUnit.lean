/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopologicalInvariance
public import WeilConjectures.TraceFormula.Specialization.NearbySliceInvariants

/-!

# Split units of `Lg^* ⊣ Rg_*`

The `toCart` part of the slice exchange reduces to the splitting of the unit `G ⟶ Rg_* Lg^* G` of
the change of geometric generic fibre `g`
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_unit`). This file
collects the formal closure properties of the class of morphisms whose unit is split at a given
complex:

* the unit of an adjunction `L ⊣ R` is a split monomorphism at `G` as soon as `G` is a retract of
  some `R H` (`CategoryTheory.Adjunction.isSplitMono_unit_app_of_retract`);
* split units compose: if the unit of `Lb^* ⊣ Rb_*` is split at `G` and that of `La^* ⊣ Ra_*` is
  split at `Lb^* G`, then the unit of `L(a ≫ b)^* ⊣ R(a ≫ b)_*` is split at `G`
  (`ProEtale.CondensedRing.isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp`);
* the unit of a universal homeomorphism is an isomorphism (topological invariance,
  `isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **Units split at retracts of the image of the right adjoint**: if `G` is a retract of `R H`,
through `s : G ⟶ R H` and `r : R H ⟶ G` with `s ≫ r = 𝟙`, then the unit `G ⟶ R L G` is a split
monomorphism, with retraction `R(s♭) ≫ r` for the adjoint `s♭ : L G ⟶ H` of `s`. -/
lemma isSplitMono_unit_app_of_retract {G : C} {H : D} (s : G ⟶ R.obj H) (r : R.obj H ⟶ G)
    (hsr : s ≫ r = 𝟙 G) : IsSplitMono (adj.unit.app G) :=
  IsSplitMono.mk' ⟨R.map ((adj.homEquiv _ _).symm s) ≫ r, by
    have h1 : adj.unit.app G ≫ R.map ((adj.homEquiv G H).symm s) = s := by
      have h2 := (adj.homEquiv G H).apply_symm_apply s
      rwa [Adjunction.homEquiv_unit] at h2
    rw [reassoc_of% h1, hsr]
    rfl⟩

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **Split units compose**: for `a : X ⟶ Y` and `b : Y ⟶ Z`, if the unit of `Lb^* ⊣ Rb_*` is a
split monomorphism at `G` and the unit of `La^* ⊣ Ra_*` is a split monomorphism at `Lb^* G`, then
the unit of `L(a ≫ b)^* ⊣ R(a ≫ b)_*` is a split monomorphism at `G`: `G` is a retract of
`Rb_* Ra_* La^* Lb^* G ≅ R(a ≫ b)_* (La^* Lb^* G)`. -/
theorem isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    [IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ b).unit.app G)]
    [IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ a).unit.app (L((b)^*⟦Λ⟧).obj G))] :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ (a ≫ b)).unit.app G) := by
  refine (derivedUpperStarLowerStarAdjunction Λ (a ≫ b)).isSplitMono_unit_app_of_retract
    (H := L((a)^*⟦Λ⟧).obj (L((b)^*⟦Λ⟧).obj G))
    ((derivedUpperStarLowerStarAdjunction Λ b).unit.app G ≫
      R((b)_*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ a).unit.app
        (L((b)^*⟦Λ⟧).obj G)) ≫ (rightDerivedLowerStarComp Λ a b).hom.app _)
    ((rightDerivedLowerStarComp Λ a b).inv.app _ ≫
      R((b)_*⟦Λ⟧).map (retraction ((derivedUpperStarLowerStarAdjunction Λ a).unit.app
        (L((b)^*⟦Λ⟧).obj G))) ≫
      retraction ((derivedUpperStarLowerStarAdjunction Λ b).unit.app G)) ?_
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, IsSplitMono.id]
  simp

/-- **Topological invariance for the unit**: for a universal homeomorphism `r`, the unit of the
derived adjunction `Lr^* ⊣ Rr_*` is an isomorphism, since `Lr^*` is an equivalence. -/
theorem isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r] :
    IsIso (derivedUpperStarLowerStarAdjunction Λ r).unit := by
  have := isEquivalence_upperStar_of_isUniversalHomeomorphism Λ r
  have : L((r)^*⟦Λ⟧).IsEquivalence :=
    Functor.isEquivalence_of_iso (leftDerivedUpperStarIsoMapDerivedCategory Λ r).symm
  exact (derivedUpperStarLowerStarAdjunction Λ r).unit_isIso_of_L_fully_faithful

/-- For a universal homeomorphism `r`, the unit of `Lr^* ⊣ Rr_*` is a split monomorphism at every
complex. -/
instance isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_of_isUniversalHomeomorphism
    {X Y : Scheme.{u}} (r : X ⟶ Y) [IsUniversalHomeomorphism r]
    (G : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ r).unit.app G) :=
  have := isIso_derivedUpperStarLowerStarAdjunction_unit_of_isUniversalHomeomorphism Λ r
  inferInstance

namespace NearbyCyclesModel

/-- **The change of geometric generic fibre up to a universal homeomorphism**: if the morphism
`g = φ.toCartesian.generic` of geometric generic fibres factors as `g = r ≫ q` with `r` a universal
homeomorphism and the unit of `Lq^* ⊣ Rq_*` is a split monomorphism at `G = Lε'^* C`, then the
pullback exchange of `φ.toCartesian` is a split monomorphism at `C`. -/
theorem Hom.isSplitMono_toCart_pullbackExchange_app_of_factor {X X' Y Y' : Scheme.{u}}
    {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (φ : M.Hom N f f')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    {Z : Scheme.{u}} (r : M.generic ⟶ Z) (q : Z ⟶ φ.cartesianModel.generic)
    [IsUniversalHomeomorphism r] (hrq : r ≫ q = φ.toCartesian.generic)
    (hq : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ q).unit.app
      ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app C) := by
  refine φ.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit Λ C ?_
  rw [← hrq]
  exact isSplitMono_derivedUpperStarLowerStarAdjunction_unit_app_comp Λ r q _

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
