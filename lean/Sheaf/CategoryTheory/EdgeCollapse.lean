/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Sheaf.CategoryTheory.Filtration

/-!
# Edge collapse and edge maps

Source: blueprint node `lem-sp-edge-collapse` (blueprint: lem-sp-edge-collapse).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

/-- (blueprint: lem-sp-edge-collapse) If a convergent exact-couple spectral sequence
    is concentrated in one column
from page `r₀` onward, then all later differentials vanish, the pages are
stationary, and the edge map is an isomorphism.

Source: blueprint node `lem-sp-edge-collapse`.
Proof: the bidegree of each differential forces both its source and target
outside the surviving column, so all differentials vanish.  The cycle and
boundary descriptions in the convergence data then identify every later page
with the initial one at `r₀` and identify the limiting page with it.  The
finite exhaustive separated filtration has only its zeroth graded piece, so
its canonical edge map is an isomorphism. -/
theorem edge_collapse
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0)
    (L : X.LimitSubobjects)
    (A : ∀ n : ℤ, X.AlphaColimit n)
    (hconv : X.ConvergesTo L A)
    (hfinite : ∀ n : ℤ, (X.imageFiltration n (A n)).IsFinite)
    (r₀ : ℕ) (hr₀ : 2 ≤ r₀)
    (hvanish : ∀ (p q : ℤ), p ≠ 0 → IsZero (X.page r₀ p q)) :
    (∀ (r : ℕ), r₀ ≤ r → ∀ (p q : ℤ),
      X.pageDifferential r p q = 0) ∧
      (∀ (r : ℕ), r₀ ≤ r → ∀ (p q : ℤ),
        ∃ (e : X.page r₀ p q ≅ X.page r p q)
          (i : (X.cycleBoundaryTower.Z (r₀ - 2) p q : C) ⟶
            (X.cycleBoundaryTower.Z (r - 2) p q : C)),
          i ≫ (X.cycleBoundaryTower.Z (r - 2) p q).arrow =
            (X.cycleBoundaryTower.Z (r₀ - 2) p q).arrow ∧
          X.cycleBoundaryTower.projection (r₀ - 2) p q ≫ e.hom =
            i ≫ X.cycleBoundaryTower.projection (r - 2) p q) ∧
      (∃ t : ∀ (p q : ℤ), X.pageInfinity L p q ≅ X.page r₀ p q,
        (∀ (p q : ℤ),
          ∃ i : (L.Z p q : C) ⟶ (X.cycleBoundaryTower.Z (r₀ - 2) p q : C),
            i ≫ (X.cycleBoundaryTower.Z (r₀ - 2) p q).arrow = (L.Z p q).arrow ∧
            cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
              (X.limitBoundary_le_cycle L p q)) ≫ (t p q).hom =
                i ≫ X.cycleBoundaryTower.projection (r₀ - 2) p q) ∧
        (∀ n : ℤ, ∃ e : (A n).obj ≅ X.page r₀ 0 n,
          eqToHom (by simp) ≫ (A n).ι 0 ≫ e.hom =
            X.toPageInfinity L 0 n ≫ (t 0 n).hom)) := by
  sorry

end CategoryTheory.BigradedExactCouple
