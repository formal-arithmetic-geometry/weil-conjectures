/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.HalfPlaneConvergence

/-!
# Canonical half-plane graded identification

Source: Stacks Project, Homology, Lemmas 12.21.4 (Tag 011T) and 12.23.5
(Tag 012F) (blueprint: lem-sp-half-plane-graded-canonical).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

-- The existential proof names in the unchanged statement are intentionally unused.
set_option linter.unusedVariables false in
/-- In the half-plane situation, the infinite-page and filtration maps are the
canonical quotient maps with the same kernel, and hence induce the canonical
associated-graded isomorphism.

Source: Stacks Project, Homology, Lemmas 12.21.4 (Tag 011T) and 12.23.5
(Tag 012F) (blueprint: lem-sp-half-plane-graded-canonical).
Proof: choose the limiting subobjects and alpha-colimits supplied by
`halfPlaneConvergence`. Extract weak convergence from its convergence conclusion;
this gives both canonical epimorphisms and equality of their kernels at every
bidegree. The theorem `g_factors_limitCycles` supplies the factorization of `g`,
and `weakConvergence_comparison` gives the unique isomorphism carrying the
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
  obtain ⟨L, A, hA, _, _, _, _, _, _, _, hConv⟩ := X.halfPlaneConvergence a hD hE
  refine ⟨L, A, hA, hConv, ?_⟩
  intro p q _ _
  have hWeak : X.WeaklyConvergesTo L A := hConv.2.1.1
  obtain ⟨hPage, hGraded, hKernel⟩ := hWeak p q
  exact ⟨X.g_factors_limitCycles L p q, hPage, hGraded, hKernel,
    X.weakConvergence_comparison L A hWeak p q⟩

end CategoryTheory.BigradedExactCouple
