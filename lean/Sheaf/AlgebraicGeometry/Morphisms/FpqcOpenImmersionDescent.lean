/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of open immersions along an fpqc covering

Source: Stacks Project, Descent, Lemma 35.23.18 (Tag 02L3)
(blueprint: lem-galois-fpqc-descend-open-immersion).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: lem-galois-fpqc-descend-open-immersion) Stacks Project, Descent,
Lemma 35.23.18 (Tag 02L3), descent direction. Open immersions are invariant under
isomorphisms of the source and target and stable under base change. They are Zariski
local on the target. In the affine faithfully flat case, descent of universal openness
and universal injectivity gives an open image; descent of isomorphisms identifies the
map over each affine open of that image. The fpqc-local criterion (Tag 02KP) then
applies to the given covering family and its pullback squares. -/
theorem isOpenImmersion_of_fpqcPrecoverage_pullback
    {T Y : Scheme.{u}} (φ : Y ⟶ T) {I : Type v} (T' : I → Scheme.{u})
    (h : ∀ i, T' i ⟶ T)
    (hh : Presieve.ofArrows T' h ∈ Scheme.fpqcPrecoverage T)
    (Y' : I → Scheme.{u}) (p : ∀ i, Y' i ⟶ Y) (φ' : ∀ i, Y' i ⟶ T' i)
    (hp : ∀ i, IsPullback (p i) (φ' i) φ (h i))
    (hφ' : ∀ i, IsOpenImmersion (φ' i)) : IsOpenImmersion φ := by
  sorry

end AlgebraicGeometry
