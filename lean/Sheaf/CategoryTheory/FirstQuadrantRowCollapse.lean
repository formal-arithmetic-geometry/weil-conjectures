/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.CategoryTheory.Filtration

/-!
# Collapse of a first-quadrant spectral sequence supported in its bottom row

Source: Stacks Project, Homology, Tags 011O and 0132; Etale Cohomology, Tag 0A4C,
second paragraph of the proof (blueprint: lem-weil-pbc-first-quadrant-row-collapse).

The stable page in total degree `n` is `n + 2`. The maps `a n r` identify page two
with page `r + 2` in bidegree `(n, 0)`. Their compatibility is stated using the
canonical cycle inclusions and homology projections, so these are the stationary
page identifications, rather than unspecified isomorphisms. The last displayed
composite is the edge map to the abutment. No separate convergence convention is used.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

/-- A first-quadrant cohomological spectral sequence supported in row zero has
isomorphic bottom edge maps to its abutment.

Source: Stacks Project, Homology, Tags 011O and 0132, and the inference in Etale
Cohomology, Tag 0A4C, second paragraph of the proof.

Proof: (1) The first-quadrant and upper-row vanishings propagate from page two to
all pages: the homology of a zero term is zero in an abelian category
(`def-sp-abelian`). (2) Both differentials at `(n, 0)` vanish on every page: the
outgoing target has negative second index and the incoming source has positive
second index. Thus cycle inclusion and homology projection are isomorphisms.
Starting with the identity, their inverses and the spectral-sequence page isomorphism
construct `a` and `b` recursively; all `a n r` are isomorphisms. (3) For `p < n`,
the graded piece of `F n` is zero by convergence and (1). The successive inclusions
of filtration steps are therefore monic and epic, hence isomorphisms. Starting
at `F⁰ = Hⁿ` gives `Fⁿ = Hⁿ`; for `n = 0` no induction is needed
(`def-sp-filtration`). Since `Fⁿ⁺¹ = 0`, the quotient projection from `Fⁿ` to its
graded piece is also an isomorphism. (4) Compose `a n n`, the inverse convergence
isomorphism, the inverse quotient projection, and the inclusion of `Fⁿ` into `Hⁿ`.
This is the edge map and every factor is an isomorphism. If the positive-degree
abutment is zero, its isomorphic page-two bottom-row terms are zero as well.
(blueprint: lem-weil-pbc-first-quadrant-row-collapse) -/
theorem first_quadrant_row_collapse
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : E₂CohomologicalSpectralSequence C)
    (hfirst : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2).X (p, q)))
    (H : ℕ → C) (F : ∀ n : ℕ, DecreasingFiltration (H n))
    (htop : ∀ n : ℕ, (F n).step 0 = ⊤)
    (hbottom : ∀ n : ℕ, (F n).step ((n : ℤ) + 1) = ⊥)
    (conv : ∀ (n p q : ℕ) (hpq : p + q = n),
      (F n).gradedPiece p ≅ (E.page ((n : ℤ) + 2)).X (p, q))
    (hrow : ∀ p q : ℤ, 0 < q → IsZero ((E.page 2).X (p, q))) :
    (∃ (a : ∀ n r : ℕ, (E.page 2).X (n, 0) ⟶
          (E.page ((r : ℤ) + 2)).X (n, 0))
       (b : ∀ n r : ℕ, (E.page 2).X (n, 0) ⟶
          (E.page ((r : ℤ) + 2)).cycles (n, 0)),
      (∀ n : ℕ, a n 0 = 𝟙 _) ∧
      (∀ n r : ℕ,
        b n r ≫ (E.page ((r : ℤ) + 2)).iCycles (n, 0) = a n r ∧
        b n r ≫ (E.page ((r : ℤ) + 2)).homologyπ (n, 0) ≫
          (E.iso ((r : ℤ) + 2) ((r : ℤ) + 3) (n, 0)).hom = a n (r + 1)) ∧
      (∀ n : ℕ, ∃ f : (E.page 2).X (n, 0) ⟶ ((F n).step n : C),
        f ≫ cokernel.π (Subobject.ofLE ((F n).step ((n : ℤ) + 1))
            ((F n).step n) ((F n).antitone_step (by omega))) =
          a n n ≫ (conv n n 0 (by omega)).inv ∧
        IsIso (f ≫ ((F n).step n).arrow))) ∧
    ((∀ n : ℕ, 0 < n → IsZero (H n)) →
      ∀ n : ℕ, 0 < n → IsZero ((E.page 2).X (n, 0))) := by
  sorry

end CategoryTheory
