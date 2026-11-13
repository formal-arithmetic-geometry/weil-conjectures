/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientFixedPullbackExact
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.ConstantScalarAlgebraicPullback

/-! # Ordinary flat sheaves under coefficient-sized inverse image

Source: Stacks Project, Tag 05VD.
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConstantScalarRestriction
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme

/-- Exact coefficient-sized inverse image preserves ordinary flat module sheaves.
 (Stacks, Tag 05VD) -/
theorem coefficientFixedPullback_preservesFlat
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    (coefficientProEtaleFixedModulePullback.{u, v} f A).PreservesFlat := by
  let J := coefficientProEtaleModelTopology.{u, v} X
  let K := coefficientProEtaleModelTopology.{u, v} Y
  let F := coefficientProEtaleModelBaseChange.{u, v} f
  have : PreservesFiniteLimits F := AlgebraicGeometry.ProEtale.model_preserves f
  have : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let L := sheafPullback F (Type (max v (u + 1))) J K
  let R := F.sheafPushforwardContinuous (Type (max v (u + 1))) J K
  let adj : L ⊣ R := sheafAdjunctionContinuous F (Type (max v (u + 1))) J K
  have : PreservesFiniteLimits L := by dsimp [L]; infer_instance
  obtain ⟨I, ⟨e⟩⟩ := exists_constantScalarAlgebraicPullback J K F A
  constructor
  intro M hM
  let S := restriction J A
  let N := S.inv.obj M
  have hN : SheafOfModules.IsFlatOnSite.{max v (u + 1), max v (u + 1),
      max v (u + 1), max v (u + 1)} (R := ring J A) N := by
    apply (CategoryTheory.ConstantScalarRestriction.flat_iff J A N).mpr
    have h := ObjectProperty.prop_of_iso ObjectProperty.flat
      (S.asEquivalence.counitIso.app M).symm hM
    exact h.2
  have hI := SheafOfModules.isFlat_algebraicInverseImageOfUniverses.{max v (u + 1),
    max v (u + 1), max v (u + 1), max v (u + 1), max v (u + 1), max v (u + 1)}
    L R adj I N hN
  have hright := (CategoryTheory.ConstantScalarRestriction.flat_iff K A (I.modules.obj N)).mp hI
  have hflat : ObjectProperty.flat ((restriction K A).obj (I.modules.obj N)) :=
    ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight _).symm hright, hright⟩
  let q := e.app N ≪≫
    (coefficientProEtaleFixedModulePullback.{u, v} f A).mapIso
      (S.asEquivalence.counitIso.app M)
  exact ObjectProperty.prop_of_iso ObjectProperty.flat q hflat

end AlgebraicGeometry.Scheme
