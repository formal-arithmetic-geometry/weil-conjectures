/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of local finite presentation along fpqc coverings

## References

* [Stacks, Tag 02KY](https://stacks.math.columbia.edu/tag/02KY)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Local finite presentation descends along an fpqc covering family of the target.
(Stacks, Tag 02KY) -/
theorem locallyOfFinitePresentation_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S)
    {I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, LocallyOfFinitePresentation (pullback.snd f (g i))) :
    LocallyOfFinitePresentation f := by
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology
    (P := @LocallyOfFinitePresentation)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
