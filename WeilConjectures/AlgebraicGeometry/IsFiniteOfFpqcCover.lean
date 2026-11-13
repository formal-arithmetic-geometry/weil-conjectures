/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Finiteness descends along fpqc covering families

## References

* Stacks Project, Descent, Tags 02LA and 02KO.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness descends along an fpqc covering family. (Stacks, Tags 02LA, 02KO) -/
theorem isFinite_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsFinite (pullback.snd f (g i))) : IsFinite f := by
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @IsFinite)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
