/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Data.Int.Interval
public import Sheaf.CategoryTheory.Filtration

/-!
# The two filtrations of a first-quadrant total complex

Source: Stacks Project, Homological Algebra, Section 12.18, Tag 012Z, and the
blueprint's two filtrations and graded pieces (blueprint: def-sp-double-complex-total).

The bicomplex and total complex are Mathlib's `HomologicalComplex₂` and `total`.
First-quadrant vanishing is a hypothesis, not extra structure. Only the two finite
supremum filtrations are new definitions. The remaining clauses are theorem statements.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- First-quadrant vanishing implies existence of the diagonal coproducts.
Source: Stacks 12.18, following Tag 012Z (blueprint: def-sp-double-complex-total).
Proof: in degree n only indices 0 ≤ p ≤ n can be nonzero. Take their finite
coproduct, extending its cocone by the unique maps from the zero objects outside
that interval. The finite coproduct universal property gives the full diagonal colimit. -/
theorem hasTotal_of_firstQuadrant
    (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  sorry

variable [K.HasTotal (ComplexShape.up ℤ)]

/-- The finite supremum defining the first filtration decreases with its index.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Proof: if p ≤ q, the interval [q,n] is contained in [p,n]. Every image in the
smaller supremum lies in the larger one; the finite supremum universal property
proves the inequality, including when either interval is empty. -/
theorem firstFiltration_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ (Finset.Icc p n).sup
      (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))) := by
  sorry

/-- Filtration by the first degree, as the finite sum of images of diagonal inclusions.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Terms past n vanish for a first-quadrant bicomplex, so this finite supremum
is exactly the stated sum over indices at least p. -/
noncomputable def firstFiltration (n : ℤ) :
    DecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))
  antitone_step := K.firstFiltration_antitone n

/-- The finite supremum defining the second filtration decreases with its index.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Proof: if p ≤ q, the interval [q,n] is contained in [p,n]. Every image in the
smaller supremum lies in the larger one; the finite supremum universal property
proves the inequality, including when either interval is empty. -/
theorem secondFiltration_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ (Finset.Icc p n).sup
      (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))) := by
  sorry

/-- Filtration by the second degree, as the finite sum of images of diagonal inclusions.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Terms past n vanish for a first-quadrant bicomplex, so this finite supremum
is exactly the stated sum over indices at least p. -/
noncomputable def secondFiltration (n : ℤ) :
    DecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))
  antitone_step := K.secondFiltration_antitone n

variable (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q))

include hK

/-- The negative degrees of the total complex vanish.
Source: Stacks 12.18, finite diagonals (blueprint: def-sp-double-complex-total).
Proof: p+q=n<0 forces p<0 or q<0, so every summand is zero. The coproduct
universal property makes the total object a zero object. -/
theorem total_isZero_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((K.total (ComplexShape.up ℤ)).X n) := by
  sorry

/-- The first filtration is preserved by the total differential.
Source: blueprint subcomplex clause (blueprint: def-sp-double-complex-total).
Proof: on each summand the total differential is the horizontal map plus the
signed vertical map. Each preserves or raises the filtered index. Each image
therefore factors through the target step, and the finite sum does too. -/
theorem firstFiltration_subcomplex (p n : ℤ) :
    ∃ f : ((K.firstFiltration n).step p : C) ⟶
      ((K.firstFiltration (n + 1)).step p : C),
      f ≫ ((K.firstFiltration (n + 1)).step p).arrow =
        ((K.firstFiltration n).step p).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n (n + 1) := by
  sorry

/-- The first filtration starts at the whole total object.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: first-quadrant vanishing leaves only the summands indexed by [0,n].
Their inclusions jointly generate the diagonal coproduct, so their image sum
is top. For n<0 both the diagonal and the empty image sum are zero. -/
theorem firstFiltration_zero (n : ℤ) : (K.firstFiltration n).step 0 = ⊤ := by
  sorry

/-- The first filtration vanishes past the diagonal.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: [n+1,n] is empty, so its finite supremum is bottom. -/
theorem firstFiltration_finite (n : ℤ) :
    (K.firstFiltration n).step (n + 1) = ⊥ := by
  sorry

/-- The canonical summand maps identify the first graded pieces and their differential.
Source: blueprint graded-piece clause (blueprint: def-sp-double-complex-total).
Proof: lift the diagonal inclusion uniquely through the step's monomorphism.
The next step is the sum of the other summands, so projecting this lift to
its cokernel is an isomorphism. Restrict the total differential to the step;
it preserves the next step as well, hence descends uniquely to the cokernel.
In the quotient the differential raising the filtered index disappears; the
remaining differential is the signed vertical map. Its square is zero because the total
differential squares to zero and the quotient maps are epimorphisms.
The equations explicitly fix the isomorphisms by the original total inclusions. -/
theorem firstFiltration_graded (p : ℤ) :
    (let F := fun n : ℤ ↦ K.firstFiltration n
    let π := fun n : ℤ ↦ cokernel.π (Subobject.ofLE ((F n).step (p + 1))
      ((F n).step p) ((F n).antitone_step (by omega)))
    ∃ (a : ∀ n : ℤ, (K.X p).X (n - p) ⟶ ((F n).step p : C))
      (f : ∀ n : ℤ, ((F n).step p : C) ⟶ ((F (n + 1)).step p : C))
      (δ : ∀ n : ℤ, (F n).gradedPiece p ⟶ (F (n + 1)).gradedPiece p),
      (∀ n : ℤ, a n ≫ ((F n).step p).arrow =
        K.ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n) ∧
      (∀ n : ℤ, IsIso (a n ≫ π n)) ∧
      (∀ n : ℤ, f n ≫ ((F (n + 1)).step p).arrow =
        ((F n).step p).arrow ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1)) ∧
      (∀ n : ℤ, π n ≫ δ n = f n ≫ π (n + 1)) ∧
      (∀ n : ℤ, (a n ≫ π n) ≫ δ n =
        ((-1 : ℤ) ^ p.natAbs • (K.X p).d (n - p) ((n + 1) - p)) ≫ (a (n + 1) ≫ π (n + 1))) ∧
      (∀ n : ℤ, δ n ≫ δ (n + 1) = 0)) := by
  sorry

/-- The second filtration is preserved by the total differential.
Source: blueprint subcomplex clause (blueprint: def-sp-double-complex-total).
Proof: on each summand the total differential is the horizontal map plus the
signed vertical map. Each preserves or raises the filtered index. Each image
therefore factors through the target step, and the finite sum does too. -/
theorem secondFiltration_subcomplex (p n : ℤ) :
    ∃ f : ((K.secondFiltration n).step p : C) ⟶
      ((K.secondFiltration (n + 1)).step p : C),
      f ≫ ((K.secondFiltration (n + 1)).step p).arrow =
        ((K.secondFiltration n).step p).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n (n + 1) := by
  sorry

/-- The second filtration starts at the whole total object.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: first-quadrant vanishing leaves only the summands indexed by [0,n].
Their inclusions jointly generate the diagonal coproduct, so their image sum
is top. For n<0 both the diagonal and the empty image sum are zero. -/
theorem secondFiltration_zero (n : ℤ) : (K.secondFiltration n).step 0 = ⊤ := by
  sorry

/-- The second filtration vanishes past the diagonal.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: [n+1,n] is empty, so its finite supremum is bottom. -/
theorem secondFiltration_finite (n : ℤ) :
    (K.secondFiltration n).step (n + 1) = ⊥ := by
  sorry

/-- The canonical summand maps identify the second graded pieces and their differential.
Source: blueprint graded-piece clause (blueprint: def-sp-double-complex-total).
Proof: lift the diagonal inclusion uniquely through the step's monomorphism.
The next step is the sum of the other summands, so projecting this lift to
its cokernel is an isomorphism. Restrict the total differential to the step;
it preserves the next step as well, hence descends uniquely to the cokernel.
In the quotient the differential raising the filtered index disappears; the
remaining differential is the horizontal map. Its square is zero because the total
differential squares to zero and the quotient maps are epimorphisms.
The equations explicitly fix the isomorphisms by the original total inclusions. -/
theorem secondFiltration_graded (p : ℤ) :
    (let F := fun n : ℤ ↦ K.secondFiltration n
    let π := fun n : ℤ ↦ cokernel.π (Subobject.ofLE ((F n).step (p + 1))
      ((F n).step p) ((F n).antitone_step (by omega)))
    ∃ (a : ∀ n : ℤ, (K.X (n - p)).X p ⟶ ((F n).step p : C))
      (f : ∀ n : ℤ, ((F n).step p : C) ⟶ ((F (n + 1)).step p : C))
      (δ : ∀ n : ℤ, (F n).gradedPiece p ⟶ (F (n + 1)).gradedPiece p),
      (∀ n : ℤ, a n ≫ ((F n).step p).arrow =
        K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n) ∧
      (∀ n : ℤ, IsIso (a n ≫ π n)) ∧
      (∀ n : ℤ, f n ≫ ((F (n + 1)).step p).arrow =
        ((F n).step p).arrow ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1)) ∧
      (∀ n : ℤ, π n ≫ δ n = f n ≫ π (n + 1)) ∧
      (∀ n : ℤ, (a n ≫ π n) ≫ δ n =
        (K.d (n - p) ((n + 1) - p)).f p ≫ (a (n + 1) ≫ π (n + 1))) ∧
      (∀ n : ℤ, δ n ≫ δ (n + 1) = 0)) := by
  sorry

end HomologicalComplex₂
