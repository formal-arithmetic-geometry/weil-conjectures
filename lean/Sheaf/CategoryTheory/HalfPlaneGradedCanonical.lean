/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.CategoryTheory.HalfPlaneConvergence

/-!
# Canonical half-plane graded identification

Source: Stacks Project, Homology, Lemmas 12.21.4 (Tag 011T) and 12.23.5
(Tag 012F) (blueprint: lem-sp-half-plane-graded-canonical).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In the half-plane situation, the infinite-page and filtration maps are the
canonical quotient maps with the same kernel, and hence induce the canonical
associated-graded isomorphism.

Source: Stacks Project, Homology, Lemmas 12.21.4 (Tag 011T) and 12.23.5
(Tag 012F) (blueprint: lem-sp-half-plane-graded-canonical).
Proof: choose the stabilized page supplied by `halfPlaneConvergence` and use
exactness of the derived couple to identify its quotient with the filtration
graded piece. The maps induced by `g` and by `alpha^p` are the two quotient
epimorphisms and have the same kernel. The first isomorphism theorem, via
`weakConvergence_comparison`, gives the unique isomorphism carrying the
infinite-page map to the filtration map.
-/
theorem halfPlaneGradedCanonical (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ (p q : ℤ), q < a → IsZero (X.D p q))
    (hE : ∀ (p q : ℤ), (p < 0 ∨ q < a) → IsZero (X.E p q)) :
    ∃ L : LimitSubobjects X, ∃ A : ∀ n : ℤ, AlphaColimit X n,
      ∃ hA : ∀ n : ℤ, (A n).obj = X.D 0 n,
      ∃ hConv : X.ConvergesTo L A,
      ∀ (p q : ℤ), 0 ≤ p → a ≤ q →
        (L.Z p q).Factors (X.initialG p q) ∧
        Epi (X.toPageInfinity L p q) ∧
        Epi (X.toGradedPiece A p q) ∧
        kernelSubobject (X.toPageInfinity L p q) =
          kernelSubobject (X.toGradedPiece A p q) ∧
        ∃! e : X.pageInfinity L p q ≅
          (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
          X.toPageInfinity L p q ≫ e.hom = X.toGradedPiece A p q := by
  sorry

end CategoryTheory.BigradedExactCouple
