/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Preadditive.Comma
import all Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
import all Submission.WeilConjectures.CategoryTheory.Sites.SmoothPurity.BinaryTorsorQuotient

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Addition of relative torsor classes
Source: Stacks Project, Tag 03AJ, injective lifting-torsor argument.
(blueprint: lem-pur-relative-torsor-pairing-addition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace AlgebraicGeometry.Etale
local instance : MorphismProperty.ContainsIdentities
    (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
  AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities

end AlgebraicGeometry.Etale
