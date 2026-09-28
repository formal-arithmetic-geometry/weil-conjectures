/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.ColimitLimit

/-!
# Colimits of limit-preserving functors

If `F : I ⥤ C ⥤ D` is a diagram of functors which all preserve limits of shape `K`, and
colimits of shape `I` in `D` commute with limits of shape `K` (i.e. the functor
`colim : (I ⥤ D) ⥤ D` preserves limits of shape `K`), then the colimit of `F` preserves
limits of shape `K`. For example, over an AB5 category a filtered colimit of left exact
functors is left exact.

## Main results

* `CategoryTheory.Limits.preservesLimitsOfShape_of_isColimit`

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/-- A colimit of functors preserving limits of shape `K` preserves limits of shape `K`,
provided colimits of shape `I` commute with limits of shape `K` in the target. -/
lemma preservesLimitsOfShape_of_isColimit {I : Type*} [Category* I] {F : I ⥤ C ⥤ D}
    (c : Cocone F) (hc : IsColimit c) (K : Type*) [Category* K] [HasColimitsOfShape I D]
    [∀ i, PreservesLimitsOfShape K (F.obj i)]
    [PreservesLimitsOfShape K (colim : (I ⥤ D) ⥤ D)] :
    PreservesLimitsOfShape K c.pt := by
  have : PreservesLimitsOfShape K F.flip :=
    preservesLimitsOfShape_of_evaluation _ _ fun i => inferInstanceAs
      (PreservesLimitsOfShape K (F.obj i))
  exact preservesLimitsOfShape_of_natIso
    ((colimitIsoFlipCompColim F).symm ≪≫ (colimit.isColimit F).coconePointUniqueUpToIso hc)

end CategoryTheory.Limits
