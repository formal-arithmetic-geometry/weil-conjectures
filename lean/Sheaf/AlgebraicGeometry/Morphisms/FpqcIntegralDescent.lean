/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover

/-!
# Descent of integral morphisms along fpqc covering families

Source: Stacks Project, Descent, Lemma 35.23.24 (Tag 02L9), descent direction
(blueprint: lem-weil-pbc-fpqc-descend-integral).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-fpqc-descend-integral) Stacks Project, Descent,
Lemma 35.23.24 (Tag 02L9): integrality descends along an fpqc covering family.

Proof for stage 3:
1. Each integral second projection is affine and universally closed by Stacks Tag 01WM
   (`pqf-lem-integral-univclosed`).
2. Universal closedness descends along the given fpqc family by Tag 02KS
   (`lem-weil-pbc-fpqc-descend-universally-closed`), so `f` is universally closed.
3. Affineness descends along the same family by Tag 02L5
   (`lem-weil-pbc-fpqc-descend-affine`), so `f` is affine.
4. Apply the reverse implication of Tag 01WM (`pqf-lem-integral-univclosed`)
   to conclude that `f` is integral. -/
theorem isIntegralHom_of_fpqcPrecoverage_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v} (S' : I → Scheme.{u})
    (g : ∀ i, S' i ⟶ S) (hcover : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (hintegral : ∀ i, IsIntegralHom (pullback.snd f (g i))) : IsIntegralHom f := by
  sorry

end AlgebraicGeometry
