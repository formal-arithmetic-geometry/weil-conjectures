/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Finiteness descends along fpqc covering families

Source: Stacks Project, Descent, Lemma Tag 02LA, descent direction of Definition Tag 02KO
(blueprint: lem-weil-pbc-fpqc-descend-finite).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness descends along an fpqc covering family.
Source: Stacks Project, Descent, Lemma Tag 02LA and Definition Tag 02KO
(blueprint: lem-weil-pbc-fpqc-descend-finite).

Proof:
1. Each second projection is integral and locally of finite type, by
   `lem-weil-pbc-finite-iff-integral-lft` (Morphisms, Tag 01WJ).
2. Integrality descends along the given fpqc covering by
   `lem-weil-pbc-fpqc-descend-integral` (Descent, Tag 02L9), so `f` is integral.
3. Local finite type descends along the same covering by
   `lem-weil-pbc-fpqc-descend-locally-finite-type` (Descent, Tag 02KX).
4. An integral morphism locally of finite type is finite, by the reverse direction of
   `lem-weil-pbc-finite-iff-integral-lft` (Morphisms, Tag 01WJ). -/
theorem isFinite_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsFinite (pullback.snd f (g i))) : IsFinite f := by
  sorry

end AlgebraicGeometry
