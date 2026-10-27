/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Fin.Basic
public import WeilConjectures.CategoryTheory.ExactCouple
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.FiniteCoconeExactCouple

/-!
# Finite filtered augmented simplex vanishing

Source: Stacks Project, Tag 012W, finite-filtration convergence, and the agent-written
augmented subset contraction in the root-tower inner-support argument
(blueprint: lem-sfb-finite-simplex-filtered-vanishing).

Increasing embeddings `Fin k ↪o I` index the subsets of cardinality `k`, including
one empty subset when `k = 0`. Finite products in an abelian category are the
canonical finite biproducts. Thus projection formulas specify the augmented
alternating subset row without selecting elements of objects of the category.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- A finite derived triangle filtration with augmented simplex first-page rows vanishes.
Source: Stacks Project, Tag 012W, finite-tail convergence, and the agent-written
simplex contraction in the root-tower inner-support proof
(blueprint: lem-sfb-finite-simplex-filtered-vanishing).

Here `F k` means `F^(k-1) D`, and `G k` means `G^(k-1)`. Only indices
`0 ≤ k ≤ m` of the triangle data are used. The row at `k = 0` is the
augmentation: its product has the unique empty embedding as index; the formula
at `k = 0` is the diagonal map. At subsequent degrees, precomposition by
`Fin.succAboveOrderEmb j` deletes the `j`-th vertex with sign `(-1)^j`.

Proof: Choose the least vertex of the nonempty finite order. In each row,
insert that vertex when absent, and use zero when it is present. At degree
zero of the reindexed row this is projection to the least vertex. Componentwise,
`dh + hd = 1`: for a subset not containing the vertex the two alternating sums
cancel except for its identity component; for a subset containing it only its
first-vertex deletion survives. The augmentation and top degree satisfy the
same identity. Thus all rows are exact, and the next spectral page is zero.
Extend the finite tower constantly below its first term and by zero above its
last term. Its exact couple in the recorded bigraded convention has
`D^(P,Q) = H^(P+Q)(F^(−Q) D)`. The diagonal colimit is `H^n(D)` with lower
isomorphic tail `P ≤ n-1` and zero upper tail `P ≥ n+m`. Apply
`BigradedExactCouple.finiteCocone_weakConvergence`. The zero limiting page
identifies with the successive quotients of the finite image filtration on
`H^n(D)`. Descending induction makes every `H^n(D)` zero, for every integer
`n`; localization at quasi-isomorphisms then makes `D` zero. A distinguished
triangle with third term isomorphic to `D` has invertible first map by the
zero-cone criterion. Finally every map between zero objects is invertible,
which gives invariance under maps of the filtered data and unique induced
maps on zero cohomology. Inverting a commuting square preserves commutativity.
No cohomological boundedness or strict chain-level graded identifications are used. -/
theorem finiteSimplex_filtered_vanishing
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{w} A]
    (I : Type t) [LinearOrder I] [Fintype I] [Nonempty I]
    (D : DerivedCategory A)
    (F G : ℕ → DerivedCategory A)
    (i : ∀ k : ℕ, F (k + 1) ⟶ F k)
    (q : ∀ k : ℕ, F k ⟶ G k)
    (δ : ∀ k : ℕ, G k ⟶ (F (k + 1))⟦(1 : ℤ)⟧)
    (hT : ∀ k : ℕ, k ≤ Fintype.card I →
      Triangle.mk (i k) (q k) (δ k) ∈ distTriang (DerivedCategory A))
    (eD : F 0 ≅ D) (hF : IsZero (F (Fintype.card I + 1)))
    (M : ℤ → A)
    (e : ∀ (b : ℤ) (k : Fin (Fintype.card I + 1)),
      (homologyFunctor A ((k.val : ℤ) - 1 + b)).obj (G k.val) ≅
        ∏ᶜ fun _ : Fin k.val ↪o I => M b)
    (he : ∀ (b : ℤ) (k : Fin (Fintype.card I)) (s : Fin (k.val + 1) ↪o I),
      (e b k.castSucc).inv ≫
        HomologySequence.δ (Triangle.mk (i k.val) (q k.val) (δ k.val))
          ((k.val : ℤ) - 1 + b) (((k.val : ℤ) - 1 + b) + 1) ≫
        (homologyFunctor A (((k.val : ℤ) - 1 + b) + 1)).map (q (k.val + 1)) ≫
        eqToHom (congrArg (fun n : ℤ => (homologyFunctor A n).obj (G (k.val + 1)))
          (by simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]; omega)) ≫
        (e b k.succ).hom ≫ Pi.π (fun _ : Fin (k.val + 1) ↪o I => M b) s =
      ∑ j : Fin (k.val + 1), (-1 : ℤ) ^ j.val •
        Pi.π (fun _ : Fin k.val ↪o I => M b) ((Fin.succAboveOrderEmb j).trans s)) :
    IsZero D ∧
      (∀ (T : Triangle (DerivedCategory A)), T ∈ distTriang (DerivedCategory A) →
        (T.obj₃ ≅ D) → IsIso T.mor₁) ∧
      (∀ (D' : DerivedCategory A), IsZero D' → ∀ f : D ⟶ D', IsIso f) := by
  sorry

end DerivedCategory
