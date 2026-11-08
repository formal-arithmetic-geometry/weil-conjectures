/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Algebra.Category.Grp.Limits

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Sections for a two-open étale cover

Source: Stacks Project, Tag 0A50, proof, first and middle spots.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
noncomputable section

private abbrev incl (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk U.ι (Category.comp_id U.ι)

end
end AlgebraicGeometry.Etale
