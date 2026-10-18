/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Upper cohomological bounds from the heart and left completeness

Source: Stacks Project, Derived Categories, Tags 08TB, 08TC, 07KC and 0H72;
Weil conjectures blueprint, det-prop-int-compactness-direct-sums, proof (2)
(blueprint: lem-sfb-left-complete-heart-upper-bound).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A uniform upper bound on a class of heart objects extends to bounded above objects
whose cohomology belongs to that class, using left completeness and preservation of
countable products. The left-completeness hypothesis is independent of the product
witness, whose existence follows from exact countable products.
Source: Stacks Project, Tags 08TB, 08TC, 07KC and 0H72, and blueprint
`det-prop-int-compactness-direct-sums`, proof (2)
(blueprint: lem-sfb-left-complete-heart-upper-bound).

Proof:
1. Exactness and the shift/cohomology isomorphism (lem-sp-derived-cohomology-shift)
show that the image of `H^i(K)[-i]` is bounded above by `i + c`.
2. Induct on `b + 1 - a`, starting from the zero truncation at `a = b + 1`.
The lower-truncation triangle (lem-pc-derived-lower-truncation-step-triangle)
and its image long exact sequence (lem-sf-derived-homology-long-exact) give the
bound `b + c` for every `T(tau_(>=a) K)`. Truncations with `a > b` are zero.
3. The successive tower layer is `H^(-n-1)(K)[n+1]`, whose image is bounded above
by `c - n - 1`. Its long exact sequence makes the transition on degree `r`
cohomology invertible for every sufficiently large `n`, namely `n >= max(0,c-r)`.
4. Exact countable products give derived products and compatibility of cohomology
with their projections (lem-weil-derived-limit-products-core). Left completeness
supplies the canonical Roos triangle of `K`. The exact product-preserving functor
carries it to the Roos triangle of its image tower (lem-pc-homotopy-limit-map).
5. For `j > b + c`, its long exact sequence and the product compatibility give
an exact segment from `1-s` on the product of degree `j-1` cohomology, through
`H^j(TK)`, to the zero product of degree `j` cohomology. It suffices that `1-s`
on the former product be an epimorphism.
6. Write this cohomology tower as `(A_n,f_n)` and choose `N` beyond which `f_n`
is invertible. On `Q = product A_n`, with projections `p_n`, put `v_N = 0`.
Define backwards `v_n = p_n + v_(n+1) >> f_n` for `n < N`, and forwards
`v_(n+1) = (v_n - p_n) >> inverse(f_n)` for `n >= N`. Every component is a finite
expression. The universal property gives `v : Q --> Q` with
`v >> (1-s) = identity`. Thus `1-s` is a split epimorphism, without enough
injectives or any elementwise argument.
7. Exactness of the segment in step 5 now gives `H^j(TK) = 0`. This uses only
finite truncation intervals and eventual invertibility to handle the negative tail;
no lower bound on `K` or on the functor is used. -/
theorem upperBound_of_heart_of_leftComplete
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts B] [CountableAB4Star B]
    (hcomplete : ∀ (K : DerivedCategory A)
      [HasProduct (fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)],
      ∃ δ : (∏ᶜ (fun n : ℕ ↦ (TStructure.t.truncGE (-(n : ℤ))).obj K)) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ (TStructure.t.natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K)
          K (Pi.lift (fun n : ℕ ↦ (TStructure.t.truncGEπ (-(n : ℤ))).app K)) δ)
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    [∀ (I : Type) [Countable I], PreservesLimitsOfShape (Discrete I) T]
    (S : Set A) (c : ℤ)
    (hheart : ∀ M : A, M ∈ S → ∀ j : ℤ, c < j →
      IsZero ((homologyFunctor B j).obj (T.obj ((singleFunctor A 0).obj M))))
    (b : ℤ) (K : DerivedCategory A)
    (hS : ∀ i : ℤ, (homologyFunctor A i).obj K ∈ S)
    (hbound : ∀ i : ℤ, b < i → IsZero ((homologyFunctor A i).obj K)) :
    ∀ j : ℤ, b + c < j → IsZero ((homologyFunctor B j).obj (T.obj K)) := by
  sorry

end DerivedCategory
