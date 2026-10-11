/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-!
# Half-plane convergence of an exact couple

Source: blueprint node thm-sp-half-plane-convergence, order 511; Stacks Project,
Tags 011T and 012F (blueprint: thm-sp-half-plane-convergence).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Half-plane exact couples stabilize and converge to the finite image filtration.
Here `pageCouple r` is the actual page `r + 2`, so the stabilization bound below
is `(r : ℤ) + 2 > max (q - a + 1) p`.

Proof, Step 1: The half-plane region implies `a ≤ q ≤ n` on total degree `n`.
The incoming differential has source first index `p - R < 0` for `R > p`,
and the outgoing differential has target second index `q - R + 1 < a` for
`R > q - a + 1`. Page cohomology therefore gives the canonical stabilization
isomorphism, and the recursive cycles and boundaries become constant, yielding
regularity and limiting subobjects (def-sp-exact-couple, def-sp-convergence).
The incoming image of `alpha^R` is zero for `R > q - a`, yielding completeness.
Exactness makes alpha an isomorphism to the left of first index zero, since both
adjacent initial E terms vanish there. Thus the diagonal colimit is `D 0 n`,
with its map from first index zero the identity. Its image filtration is zero
for `q < a` and the whole object for `q ≥ n`.

Step 2: For `p ≥ 0`, choose a stabilized page `R` with `u = p - R + 2 ≤ 0`
and `v = q + R - 2`. By lem-sp-derived-couple-exact, the iterated D image
at `(u,v)` identifies with `G_q`, and its incoming alpha image with `G_(q-1)`.
The next D term is zero because its incoming source has second index below a.
Exactness gives `E_R = G_q / G_(q-1)`, hence the graded piece of `F` in
sense of def-sp-filtration. Iterating the defining equation for derived g shows
that the two canonical maps from `D p q` are onto with equal kernels; thus
this is the canonical comparison of def-sp-convergence. For `p < 0`, both
sides are zero. The finite filtration is exhaustive, separated and complete
in the inverse-limit sense, proving convergence.

Step 3: Compare the cycle/boundary formulas in Stacks Tag 011T and the
infinite-page and associated-graded discussion in Tag 012F.
Source: blueprint node thm-sp-half-plane-convergence, order 511; Stacks Project,
Tags 011T and 012F (blueprint: thm-sp-half-plane-convergence). -/
theorem halfPlaneConvergence
    (X : BigradedExactCouple C 0) (a : ℤ)
    (hD : ∀ (p q : ℤ), q < a → IsZero (X.D p q))
    (hE : ∀ (p q : ℤ), (p < 0 ∨ q < a) → IsZero (X.E p q)) :
    ∃ L : LimitSubobjects X, ∃ A : ∀ n : ℤ, AlphaColimit X n,
      ∃ hA : ∀ n : ℤ, (A n).obj = X.D 0 n,
      (∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
        eqToHom (by congr 1; omega)) ∧
      (∀ (r : ℕ) (n p q : ℤ), p + q = n →
        ¬ IsZero ((X.pageCouple r).E p q) → a ≤ q ∧ q ≤ n) ∧
      (∀ (r : ℕ) (p q : ℤ),
        (r : ℤ) + 2 > max (q - a + 1) p →
          ∃ e : (X.pageCouple r).E p q ≅ (X.pageCouple (r + 1)).E p q,
            kernel.ι ((X.pageCouple r).d p q) ≫ e.hom =
              (X.pageCouple r).derivedEProjection p q) ∧
      (∀ (n p : ℤ), p ≤ 0 → (X.imageFiltration n (A n)).step p = ⊤) ∧
      (∀ n : ℤ, (X.imageFiltration n (A n)).IsFinite ∧
        (X.imageFiltration n (A n)).IsExhaustive ∧
        (X.imageFiltration n (A n)).IsSeparated) ∧
      (∀ (p q : ℤ),
        ∃ e : X.pageInfinity L p q ≅
          (X.imageFiltration (p + q) (A (p + q))).gradedPiece p,
          X.toPageInfinity L p q ≫ e.hom = X.toGradedPiece A p q) ∧
      X.IsComplete ∧ X.ConvergesTo L A := by
  sorry

end CategoryTheory.BigradedExactCouple
