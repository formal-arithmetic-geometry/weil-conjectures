/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Flatness descends along fpqc covering families

## References

* Stacks Project, Tags 02L2 and 02KO
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flatness descends along an fpqc covering family (Stacks, Descent, Tag 02L2). -/
theorem flat_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, Flat (pullback.snd f (g i))) : Flat f := by
  apply Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @Flat) ?_ f
    (fun i => pullback.fst f (g i)) (fun i => pullback.snd f (g i))
    (fun i => IsPullback.of_hasPullback f (g i)) h
  exact Precoverage.generate_mem_toGrothendieck hg

end AlgebraicGeometry
