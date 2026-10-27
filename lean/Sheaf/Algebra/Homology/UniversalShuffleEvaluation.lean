/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.BicosimplicialShuffleObjects
public import Sheaf.AlgebraicTopology.UniversalShuffleHomotopyInverse

/-! # Evaluation of the universal bisimplex shuffle on cochain diagrams

Source: the finite representable evaluation argument in steps 6–7 of the shuffle
proof in direct-images paragraph (3).
(blueprint: lem-sfb-universal-shuffle-evaluation).
-/

@[expose] public section
set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits AlgebraicTopology.FreeBisimplex
open scoped Simplicial

namespace AlgebraicTopology.BicosimplicialShuffle

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Evaluating a fixed, generator-normalized universal shuffle homotopy equivalence
on an arbitrary abelian cochain diagram gives the displayed signed finite-subset map.
This is a transfer result: the universal equivalence and both boundary formulas are inputs;
it does not construct the universal map or prove either resolution exact.

Source: direct-images paragraph (3), shuffle proof steps 6–7; finite representable matrix
algebra of `lem-sfb-finite-representable-matrix-totalization`.
(blueprint: lem-sfb-universal-shuffle-evaluation).

Proof: identify the small-universe free bisimplex representable with the singleton
finite-list representable by the free abelian map removing ULift. Reindex Q_n's finite
antidiagonal sum by a list of length n+1. Conjugate the differentials and the fixed
universal maps and homotopies along these isomorphisms. This gives chain complexes in
FiniteFreeRepresentables and the same homotopy equivalence there, since its inclusion
in the diagram category is fully faithful and additive. Apply finite representable
matrix totalization. The evaluation isomorphisms and the antidiagonal coproduct
universal properties identify the two evaluated total functors naturally with D and T.
On P the generator boundary is the diagonal alternating coface sum. On Q it is the
separate sum with sign (-1)^a; internal totalization contributes (-1)^(a+b).
Thus the identifications commute with differentials, including when a direction is zero.
The matrix formula evaluates each universal generator arrow to the corresponding
X-map. A lattice path is uniquely the subset of positions of its horizontal steps;
its complement records vertical steps. Its two counting arrows are shuffleSurjection,
and its vertical-before-horizontal inversions are exactly those counted by shuffleSign.
Reindexing the finite path sum gives the stated sum over all subsets of Fin n.
The evaluated inverse and homotopies give the asserted homotopy equivalences; their
internal differential terms cancel with signs (-1)^(n-1) and (-1)^n. Matrix evaluation
is natural in X, as are the coproduct identifications. Empty subsets, zero factors,
constant directions, and zero objects require no separate nonvanishing hypothesis. -/
theorem evaluate_universal_shuffle
    (P Q : ChainComplex (SimplexCategory × SimplexCategory ⥤ AddCommGrpCat.{0}) ℕ)
    (p : ∀ n : ℕ, P.X n ≅ FreeBisimplex.representable.{0} (⦋n⦌, ⦋n⦌))
    (q : ∀ n : ℕ, Q.X n ≅ FreeBisimplex.totalTerm.{0} n)
    (hP : ∀ (n : ℕ) (j : SimplexCategory × SimplexCategory)
      (α : (⦋n + 1⦌, ⦋n + 1⦌) ⟶ j),
      (p n).hom.app j ((P.d (n + 1) n).app j
        ((p (n + 1)).inv.app j (generator α))) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ k.val •
        generator ((SimplexCategory.δ k, SimplexCategory.δ k) ≫ α))
    (hQ : ∀ (a b : ℕ) (j : SimplexCategory × SimplexCategory)
      (α : (⦋a⦌, ⦋b⦌) ⟶ j),
      (q (a + b - 1)).hom.app j ((Q.d (a + b) (a + b - 1)).app j
        ((q (a + b)).inv.app j (totalGenerator a b (a + b) rfl j α))) =
      totalBoundary a b j α)
    (e : HomotopyEquiv Q P)
    (hσ : ∀ (a b : ℕ) (j : SimplexCategory × SimplexCategory)
      (α : (⦋a⦌, ⦋b⦌) ⟶ j),
      (p (a + b)).hom.app j ((e.hom.f (a + b)).app j
        ((q (a + b)).inv.app j (totalGenerator a b (a + b) rfl j α))) =
      shuffleGenerator a b j α) :
    ∃ F : ∀ X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ,
        HomotopyEquiv (diagonalTotal X) (successiveTotal X),
      ∀ (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
        (n r m : ℕ) (h : n + r = m),
        diagonalInclusion X n r m h ≫ (F X).hom.f m =
          ∑ μ : Finset (Fin n), shuffleTerm X n r m h μ := by sorry

end AlgebraicTopology.BicosimplicialShuffle
