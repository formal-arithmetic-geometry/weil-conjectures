/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Etale descent along fpqc coverings

## References

* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Descent direction of Stacks, Descent, Lemma 02VN: if every base change of `f` along an
fpqc covering is etale, then `f` is etale. -/
theorem etale_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, Etale (pullback.snd f (g i))) : Etale f := by
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @Etale)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
