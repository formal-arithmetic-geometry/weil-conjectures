/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Sheaf.CategoryTheory.CoefficientFixedScalarsLocalModels
import all Sheaf.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback

/-! # Exact inverse image of fixed-scalar coefficient sheaves

Source: Stacks Project, Sites, Tags 00YV and 00WJ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Fixed-scalar scheme inverse image is a left adjoint and preserves colimits.
Source: Stacks Tag 00YV (blueprint: lem-sfb-coefficient-fixed-pullback-exact). -/
instance coefficientFixedPullback_colimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    PreservesColimits (coefficientProEtaleFixedModulePullback.{u, v} f A) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (coefficientProEtaleModelBaseChange.{u, v} f) (ModuleCat A)
    (coefficientProEtaleModelTopology.{u, v} X)
    (coefficientProEtaleModelTopology.{u, v} Y)).leftAdjoint_preservesColimits

/-- Scheme base change is left exact on fixed-scalar sheaves.
Source: Stacks Tags 00YV and 00WJ
(blueprint: lem-sfb-coefficient-fixed-pullback-exact). -/
instance coefficientFixedPullback_limits {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    PreservesFiniteLimits (coefficientProEtaleFixedModulePullback.{u, v} f A) := by
  have : PreservesFiniteLimits (coefficientProEtaleModelBaseChange.{u, v} f) :=
    AlgebraicGeometry.ProEtale.model_preserves f
  have : RepresentablyFlat (coefficientProEtaleModelBaseChange.{u, v} f) :=
    flat_of_preservesFiniteLimits _
  unfold coefficientProEtaleFixedModulePullback
  infer_instance

/-- Exact inverse image of module-valued sheaves is additive.
Source: Stacks Tag 00YV (blueprint: lem-sfb-coefficient-fixed-pullback-exact). -/
instance coefficientFixedPullback_additive {X Y : Scheme.{u}} (f : Y ⟶ X)
    (A : Type (max v (u + 1))) [CommRing A] :
    (coefficientProEtaleFixedModulePullback.{u, v} f A).Additive :=
  Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry.Scheme
