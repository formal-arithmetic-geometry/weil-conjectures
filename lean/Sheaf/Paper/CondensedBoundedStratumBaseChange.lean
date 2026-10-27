/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.CondensedStratumBaseChangeCalculus

/-! # Bounded exact stratum base change for condensed coefficients

Source: Stacks Project, Tags 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-bounded-stratum-base-change)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange

private instance pullback_additive
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).Additive :=
  inferInstanceAs (CondensedRing.upperStar Λ f).mapDerivedCategory.Additive

set_option maxHeartbeats 1600000 in
-- The conjunction elaborates the exactness witnesses and both bounded mate comparisons.
/-- The exact open and closed exchange calculus restricted to all bounded inputs.
Source: Stacks 09AA, 09BM, 09BN and 09AH; blueprint Local models.
(blueprint: lem-sfb-condensed-bounded-stratum-base-change).

Proof: obtain exact closed direct image and invertible counits from recollement.
The cartesian open-square support argument makes the open mate invertible; the
complementary restrictions detect invertibility of the closed mate. Whisker both
isomorphisms by the bounded inclusion. Exact-functor homology preserves both
bounds. The Hom-adjunction identities normalize the restrictions, and the mixed
restrictions vanish by support and pullback composition. Uniqueness of maps from
a zero object gives the displayed zero maps.
-/
theorem bounded_open_closed_base_change
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U Z T Up Zp Tp : Scheme.{u}}
    {h : Tp ⟶ T} {j : U ⟶ T} {i : Z ⟶ T}
    {hU : Up ⟶ U} {jp : Up ⟶ Tp} {hZ : Zp ⟶ Z} {ip : Zp ⟶ Tp}
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    [IsOpenImmersion jp] [IsClosedImmersion ip] [QuasiCompact jp]
    (hcomp : Set.range j = (Set.range i)ᶜ)
    (sqU : IsPullback hU jp j h) (sqZ : IsPullback hZ ip i h) :
    Exists fun [_hi : PreservesFiniteColimits (CondensedRing.lowerStar Λ i)] ↦
    Exists fun [_hip : PreservesFiniteColimits (CondensedRing.lowerStar Λ
            ip)] ↦
      (∃ beta : DerivedCategory.Bounded.ι ⋙ ((pullback Λ hU) ⋙
            (openExtension Λ jp)) ≅
          DerivedCategory.Bounded.ι ⋙ ((openExtension Λ j) ⋙
            (pullback Λ h)),
        beta.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (openMate
            Λ
            sqU.toCommSq)) ∧
      (∃ gamma : DerivedCategory.Bounded.ι ⋙ ((closedDirectImage Λ
            i) ⋙
            (pullback Λ h)) ≅
          DerivedCategory.Bounded.ι ⋙ ((pullback Λ hZ) ⋙
            (closedDirectImage Λ ip)),
        gamma.hom = Functor.whiskerLeft DerivedCategory.Bounded.ι (closedMate
            Λ
            sqZ.toCommSq)) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
            (condensedRingObj Λ U)),
        DerivedCategory.TStructure.t.bounded
            (((pullback Λ hU) ⋙
            (openExtension Λ jp)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((openExtension Λ j)
            ⋙ (pullback Λ h)).obj N.obj) ∧
        IsIso ((openAdjunction Λ jp).unit.app ((pullback
            Λ hU).obj
            N.obj)) ∧
        IsIso ((openAdjunction Λ j).unit.app N.obj) ∧
        (openAdjunction Λ jp).unit.app
            ((pullback Λ hU).obj N.obj) ≫
            (pullback Λ jp).map
            ((openMate
            Λ sqU.toCommSq).app N.obj) =
          (pullback Λ hU).map
            ((openAdjunction Λ j).unit.app N.obj) ≫
            (pullbackSquare Λ sqU.toCommSq).hom.app
            ((openExtension Λ j).obj N.obj) ∧
        IsZero ((pullback Λ ip).obj
          (((pullback Λ hU) ⋙
            (openExtension Λ jp)).obj N.obj)) ∧
        IsZero ((pullback Λ ip).obj
          (((openExtension Λ j) ⋙
            (pullback Λ h)).obj N.obj)) ∧
        (pullback Λ ip).map
            ((openMate
            Λ
            sqU.toCommSq).app N.obj) = 0) ∧
      (∀ N : DerivedCategory.Bounded
          (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
            (condensedRingObj Λ Z)),
        DerivedCategory.TStructure.t.bounded
            (((closedDirectImage Λ i) ⋙
            (pullback Λ h)).obj N.obj) ∧
        DerivedCategory.TStructure.t.bounded
            (((pullback Λ hZ) ⋙
            (closedDirectImage Λ ip)).obj N.obj) ∧
        IsIso ((closedAdjunction Λ i).counit.app N.obj) ∧
        IsIso ((closedAdjunction Λ ip).counit.app ((pullback
            Λ hZ).obj N.obj)) ∧
        (pullback Λ ip).map
            ((closedMate
            Λ sqZ.toCommSq).app N.obj) ≫
            (closedAdjunction Λ ip).counit.app ((pullback
            Λ hZ).obj N.obj) =
          (pullbackSquare Λ sqZ.toCommSq).inv.app
            ((closedDirectImage Λ i).obj N.obj) ≫
            (pullback Λ hZ).map
            ((closedAdjunction Λ i).counit.app N.obj) ∧
        IsZero ((pullback Λ jp).obj
          (((closedDirectImage Λ i) ⋙
            (pullback Λ h)).obj N.obj)) ∧
        IsZero ((pullback Λ jp).obj
          (((pullback Λ hZ) ⋙
            (closedDirectImage Λ ip)).obj N.obj)) ∧
        (pullback Λ jp).map
            ((closedMate
            Λ sqZ.toCommSq).app N.obj) = 0) := by
  have hcomp' := complementary_base_change hcomp sqU sqZ
  obtain ⟨hi, hci⟩ := closed_data Λ i j hcomp
  obtain ⟨hip, hcip⟩ := closed_data Λ ip jp hcomp'
  have hdi : IsIso (closedAdjunction Λ i).counit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  have hdip : IsIso (closedAdjunction Λ ip).counit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_counit _
  have hβ := open_mate_iso Λ sqU
  have hγ := closed_mate_iso Λ hcomp hcomp' sqU.toCommSq sqZ.toCommSq hdi hdip
  refine ⟨hi, hip, ⟨Functor.isoWhiskerLeft _ (asIso (openMate Λ sqU.toCommSq)), rfl⟩,
    ⟨Functor.isoWhiskerLeft _ (asIso (closedMate Λ sqZ.toCommSq)), rfl⟩, ?_, ?_⟩
  · intro N
    have hu := open_unit_iso Λ j
    have hup := open_unit_iso Λ jp
    have hz₁ := mixed_open_zero Λ jp ip
      (by rw [hcomp']; exact disjoint_compl_left) ((pullback Λ hU).obj N.obj)
    have hz₂ := ((pullback Λ hZ).map_isZero
      (mixed_open_zero Λ j i (by rw [hcomp]; exact disjoint_compl_left) N.obj)).of_iso
        ((pullbackSquare Λ sqZ.toCommSq).symm.app ((openExtension Λ j).obj N.obj))
    refine ⟨(CondensedRing.openImmersionLowerShriek Λ jp).bounded_mapDerivedCategory_obj
        ((CondensedRing.upperStar Λ hU).bounded_mapDerivedCategory_obj N.property),
      (CondensedRing.upperStar Λ h).bounded_mapDerivedCategory_obj
        ((CondensedRing.openImmersionLowerShriek Λ j).bounded_mapDerivedCategory_obj
          N.property), inferInstance, inferInstance, ?_, hz₁, hz₂, hz₁.eq_of_src _ _⟩
    exact open_mate_unit _ _ _ _
  · intro N
    have hz₁ := ((pullback Λ hU).map_isZero
      (mixed_closed_zero Λ i j
        (by rw [hcomp]; exact disjoint_compl_left) N.obj)).of_iso
          ((pullbackSquare Λ sqU.toCommSq).symm.app
            ((closedDirectImage Λ i).obj N.obj))
    have hz₂ := mixed_closed_zero Λ ip jp
      (by rw [hcomp']; exact disjoint_compl_left) ((pullback Λ hZ).obj N.obj)
    refine ⟨(CondensedRing.upperStar Λ h).bounded_mapDerivedCategory_obj
        ((CondensedRing.lowerStar Λ i).bounded_mapDerivedCategory_obj N.property),
      (CondensedRing.lowerStar Λ ip).bounded_mapDerivedCategory_obj
        ((CondensedRing.upperStar Λ hZ).bounded_mapDerivedCategory_obj N.property),
      inferInstance, inferInstance, ?_, hz₁, hz₂, hz₁.eq_of_src _ _⟩
    exact closed_mate_counit _ _ _ _


end AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange
