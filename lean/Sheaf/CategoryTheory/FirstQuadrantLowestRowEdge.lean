/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-!
# The lowest-row edge of a first-quadrant spectral sequence

Source: Stacks Project, Homology, Tags 011N, 011O, 0121 and 0132
(blueprint: lem-pur-first-quadrant-lowest-row-edge).

The stable term at `(p,q)` of total degree `n` is represented on page `n+2`.
The convergence identifications are transported along the canonical stabilization
comparison to this representative of the recursive cycle/boundary quotient.
The conclusion specifies stationary page comparisons by their cycle inclusions
and homology projections, and specifies the edge by its quotient square.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The lowest-row edge is an isomorphism, with its canonical survival comparisons.
Source: Stacks Project, Homology, Tags 011N, 011O, 0121 and 0132
(blueprint: lem-pur-first-quadrant-lowest-row-edge).

Proof:
1. The zeros outside the first quadrant and below row `m` propagate through all
   pages, since a subquotient of a zero object is zero (`def-sp-abelian`,
   `def-sp-spectral-sequence`).
2. At `(0,m)` every incoming source has negative first index. Every outgoing
   target has second index less than `m`. Thus both differentials vanish.
   The recursive cycles remain the whole initial entry and boundaries remain zero
   (`def-sp-convergence`). Starting with the identity, lift to cycles and project
   to homology using the page isomorphism. This gives exactly `a` and `b` below,
   so `a m` is the canonical survival isomorphism to the stable page `m+2`.
3. For `1 ≤ p ≤ m`, the stable term `(p,m-p)` vanishes, so the supplied convergence
   comparison makes the corresponding graded piece zero (`def-sp-filtration`).
4. Descend from `F^(m+1) = 0`: a monomorphism with zero cokernel is an isomorphism
   in an abelian category. Thus successive filtration steps agree and `F^1 = 0`.
   For `m=0` this is already the terminal filtration hypothesis.
5. The edge is quotient from `F^0 = H^m`, followed by the supplied convergence
   comparison and the inverse stationary comparison. Its defining quotient square
   is displayed below. Quotient by the now zero `F^1` is an isomorphism; hence
   every factor, and therefore this particular edge, is an isomorphism.
-/
theorem first_quadrant_lowest_row_edge
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : E₂CohomologicalSpectralSequence C)
    (hfirst : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p, q)))
    (H : ℕ → C) (F : ∀ n : ℕ, DecreasingFiltration (H n))
    (htop : ∀ n : ℕ, (F n).F 0 = ⊤)
    (hbottom : ∀ n : ℕ, (F n).F ((n : ℤ) + 1) = ⊥)
    (conv : ∀ (n p q : ℕ) (_hpq : p + q = n),
      (F n).gr p ≅ (E.page ((n : ℤ) + 2)).X (p, q))
    (m : ℕ)
    (hrow : ∀ p q : ℕ, q < m → IsZero ((E.page 2).X (p, q))) :
    ∃ (a : ∀ r : ℕ, (E.page 2).X (0, m) ≅
          (E.page ((r : ℤ) + 2)).X (0, m))
      (b : ∀ r : ℕ, (E.page 2).X (0, m) ⟶
          (E.page ((r : ℤ) + 2)).cycles (0, m)),
      (a 0).hom = 𝟙 _ ∧
      (∀ r : ℕ,
        b r ≫ (E.page ((r : ℤ) + 2)).iCycles (0, m) = (a r).hom ∧
        b r ≫ (E.page ((r : ℤ) + 2)).homologyπ (0, m) ≫
          (E.iso ((r : ℤ) + 2) ((r : ℤ) + 3) (0, m)).hom = (a (r + 1)).hom) ∧
      (F m).F 1 = ⊥ ∧
      ∃ edge : H m ⟶ (E.page 2).X (0, m),
        ((F m).F 0).arrow ≫ edge ≫ (a m).hom =
          cokernel.π (Subobject.ofLE _ _ ((F m).F_succ_le 0)) ≫
            (conv m 0 m (by omega)).hom ∧ IsIso edge := by
  sorry

end CategoryTheory
