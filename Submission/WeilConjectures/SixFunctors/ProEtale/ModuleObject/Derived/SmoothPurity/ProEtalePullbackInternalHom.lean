/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Internal Hom and weakly etale coefficient pullback

Source: the localization calculation for internal Hom, blueprint stratum Hom step 3.
(blueprint: lem-proetale-pullback-internal-hom)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

attribute [local irreducible] Mod.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing
universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
/-- Coefficient inverse image is strong monoidal for the relative module tensor.
Source: blueprint stratum Hom lemma, proof step 3, restriction of evaluation.
(blueprint: lem-proetale-pullback-internal-hom). -/
noncomputable instance supportPullback_monoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (supportPullback Λ f).Monoidal := by
  unfold supportPullback
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
