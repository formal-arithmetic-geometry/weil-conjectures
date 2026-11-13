/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.SeparatedOpenInduction
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenIntersectionProperty

/-!
# Induction principle for quasi-compact opens

## References

* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry

/-- Induction for quasi-compact opens of a quasi-compact quasi-separated scheme: a property
holding for affine opens and stable under the union `U ⊔ V` of a quasi-compact open `U` and an
affine open `V` (given it holds on `U`, `V`, `U ⊓ V`) holds for every quasi-compact open. -/
theorem quasiCompactOpen_induction (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (P : X.Opens → Prop)
    (h_affine : ∀ U : X.Opens, IsAffineOpen U → P U)
    (h_union : ∀ (U V : X.Opens), IsCompact (U : Set X) → IsAffineOpen V →
      P U → P V → P (U ⊓ V) → P (U ⊔ V)) :
    ∀ U : X.Opens, IsCompact (U : Set X) → P U := by
  intro U hU
  refine compact_open_induction_on U hU ?_ ?_
  · exact h_affine _ (isAffineOpen_bot X)
  · exact fun S hS V hPS ↦ h_union S (V : X.Opens) hS V.property hPS
      (h_affine _ V.property)
      (property_intersection_of_quasiCompact_affine X P h_affine h_union S
        (V : X.Opens) hS V.property)

end AlgebraicGeometry
