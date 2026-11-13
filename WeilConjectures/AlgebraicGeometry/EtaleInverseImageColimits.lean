/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Colimits and inverse image of abelian étale sheaves

Source: Stacks Project, Categories, Lemma 0038(1), applied to the inverse-image
adjunction of Étale Cohomology, Definition 03Q0; Étale Cohomology, proof of Lemma 0A4B.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Inverse image of abelian sheaves on small étale sites preserves every small colimit.
(Stacks, Tags 0038 and 0A4B). -/
theorem inverseImage_preservesColimits {U V : Scheme.{u}} (f : U ⟶ V) :
    PreservesColimitsOfSize.{w, w} (upperStar AddCommGrpCat.{u + 1} f) := by
  exact (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).leftAdjoint_preservesColimits

end AlgebraicGeometry.Etale
