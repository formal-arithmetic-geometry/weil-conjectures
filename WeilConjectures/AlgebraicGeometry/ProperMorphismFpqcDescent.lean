/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Proper morphisms descend along fpqc covering families

## References

* [Stacks Project, Tag 02L1](https://stacks.math.columbia.edu/tag/02L1)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Properness descends along an fpqc covering family (Stacks, Tag 02L1). -/
theorem isProper_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsProper (pullback.snd f (g i))) : IsProper f := by
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @IsProper)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
