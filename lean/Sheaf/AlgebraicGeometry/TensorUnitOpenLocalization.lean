/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Localization of the tensor-pullback unit on an open set

Source: Stacks Project, Tags 0096 and 01E8, local degree-zero projection formula.
(blueprint: lem-sc-tensor-unit-open-localization)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The pullback-pushforward functor and its adjunction unit restrict to an
additive endofunctor and a natural transformation on the open slice site.
Source: Stacks Project, Tag 0096 (adjunction) and Tag 01E8 (local calculation).
(blueprint: lem-sc-tensor-unit-open-localization)

Proof: Set V = p^{-1}U and restrict the morphism of ringed spaces to V → U.
Take H to be its tensor pullback followed by direct image, and α its adjunction
unit. Tensor pullback is a left adjoint between additive categories; direct image
acts sectionwise by restriction of scalars. Hence both are additive and so is H.
Restriction of direct image is direct image from V: both assign to W contained
in U the sections on p^{-1}W with the same scalar action. Tensor pullback commutes
with restriction: the opens contained in U are cofinal in the inverse-image
neighbourhoods of any open in V; extension of scalars uses the same restricted
ring maps, and sheafification commutes with open restriction. Compose these
comparisons to obtain θ. The prescribed unit sends m to 1 tensor m before
sheafification in both constructions, so restriction of that formula gives the
asserted equality for each M. The comparisons commute with module morphisms,
hence θ is natural. This argument permits an empty U and makes no local-freeness
or invertibility assumption. -/
theorem tensorPullback_unit_open_localization {X Y : Scheme.{u}} (p : X ⟶ Y)
    (U : Opens Y) :
    ∃ (H : SheafOfModules.{u} (Y.ringCatSheaf.over U) ⥤
        SheafOfModules.{u} (Y.ringCatSheaf.over U))
      (α : 𝟭 _ ⟶ H)
      (θ : SheafOfModules.overFunctor Y.ringCatSheaf U ⋙ H ≅
        Modules.tensorPullback p ⋙ Modules.pushforward p ⋙
          SheafOfModules.overFunctor Y.ringCatSheaf U),
      H.Additive ∧ ∀ M : Y.Modules,
        ((Classical.choose (Modules.exists_tensorPullbackAdjunction p)).unit.app M).over U =
          α.app (M.over U) ≫ θ.hom.app M := by sorry

end AlgebraicGeometry.Scheme
