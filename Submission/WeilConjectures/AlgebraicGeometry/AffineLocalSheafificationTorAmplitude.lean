/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteTorDimension
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import Submission.WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import Submission.WeilConjectures.AlgebraicGeometry.OpenImmersionTensorVanishingTest
import all Submission.WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Tor bounds for an affine module model

Source: Stacks Project, Tags 08CG, 08E9 and 08DX.
(blueprint: lem-pc-affine-local-sheafification-tor-amplitude).
-/

@[expose] public section

universe u w wR

open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.Scheme

noncomputable def affine_cancel (S : Scheme.{u}) (U : S.Opens) (hU : IsAffineOpen U) :
    affinePerfectSheafification S U hU ⋙ (Modules.overEquiv U).functor ⋙
      Modules.restrictFunctor hU.isoSpec.inv ≅ tilde.functor (S.presheaf.obj (.op U)) := by
  let T := tilde.functor (S.presheaf.obj (.op U))
  let H := Modules.restrictFunctor hU.isoSpec.hom
  let B := Modules.restrictFunctor hU.isoSpec.inv
  let E := Modules.overEquiv U
  change ((T ⋙ H) ⋙ E.inverse) ⋙ E.functor ⋙ B ≅ T
  exact Functor.isoWhiskerLeft (T ⋙ H) (Functor.isoWhiskerRight E.counitIso B) ≪≫
    Functor.isoWhiskerLeft T
      ((Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom).symm ≪≫
        Modules.restrictFunctorCongr hU.isoSpec.inv_hom_id ≪≫ Modules.restrictFunctorId) ≪≫
    Functor.rightUnitor T

end AlgebraicGeometry.Scheme
