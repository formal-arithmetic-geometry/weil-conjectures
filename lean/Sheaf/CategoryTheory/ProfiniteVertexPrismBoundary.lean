/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData

/-! # Alternating operators on profinite tuples

Source: Stacks Project, simplicial.tex, Tag 019S, equation-homotopy-to-homotopy,
contravariant tuple adaptation (blueprint: lem-sfb-profinite-vertex-prism-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Preadditive
namespace CategoryTheory.CondensedBar.TupleOperators

/-- Delete the indicated coordinate. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
def deletion (Z : Profinite.{u}) (n : ℕ) (i : Fin (n + 2)) :
    power Z (n + 2) ⟶ power Z (n + 1) :=
  CompHausLike.ofHom _ ⟨fun x j ↦ x (i.succAbove j),
    continuous_pi fun j ↦ continuous_apply (i.succAbove j)⟩

/-- Apply a parameter map in every coordinate. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
def coordinate {X Y : Profinite.{u}} (a : C(X, Y)) (n : ℕ) :
    power X (n + 1) ⟶ power Y (n + 1) :=
  CompHausLike.ofHom _ ⟨fun x j ↦ a (x j),
    continuous_pi fun j ↦ a.continuous.comp (continuous_apply j)⟩

/-- The continuous map inserting the two images of one vertex. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
def insertion {X Y : Profinite.{u}} (a b : C(X, Y)) (n : ℕ) (i : Fin (n + 1)) :
    power X (n + 1) ⟶ power Y (n + 2) :=
  CompHausLike.ofHom _ ⟨fun x j ↦ if j.val ≤ i.val then a (x (i.predAbove j))
    else b (x (i.predAbove j)), continuous_pi fun j ↦ by
      split_ifs
      · exact a.continuous.comp (continuous_apply _)
      · exact b.continuous.comp (continuous_apply _)⟩

/-- The simplicial object of nonempty tuples. Source: the deletion construction, Stacks 0194
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
def tuples (Z : Profinite.{u}) : SimplicialObject Profinite.{u} where
  obj n := power Z (n.unop.len + 1)
  map f := CompHausLike.ofHom _ ⟨fun x j ↦ x (f.unop.toOrderHom j),
    continuous_pi fun j ↦ continuous_apply _⟩
  map_id _ := by ext x j; rfl
  map_comp _ _ := by ext x j; rfl

variable {C : Type w} [Category.{v} C] [Preadditive C]

/-- The alternating deletion operator for any contravariant functor. Source: Stacks 0194
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
def differential (H : Profinite.{u}ᵒᵖ ⥤ C) (Z : Profinite.{u}) (n : ℕ) :
    H.obj (op (power Z (n + 1))) ⟶ H.obj (op (power Z (n + 2))) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • H.map (deletion Z n i).op

/-- The signed sum of the vertex insertion maps. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
def prism (H : Profinite.{u}ᵒᵖ ⥤ C) {X Y : Profinite.{u}}
    (a b : C(X, Y)) (n : ℕ) :
    H.obj (op (power Y (n + 2))) ⟶ H.obj (op (power X (n + 1))) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • H.map (insertion a b n i).op

/-- Alternating deletion is the differential of the tuple cosimplicial object.
Source: Mathlib alternating coface construction (blueprint:
lem-sfb-profinite-vertex-prism-boundary). -/
theorem differential_eq (H : Profinite.{u}ᵒᵖ ⥤ C) (Z : Profinite.{u}) (n : ℕ) :
    differential H Z n =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD ((tuples Z).rightOp ⋙ H) n := rfl

/-- Deletion squared vanishes by the Mathlib alternating coface construction.
Source: Stacks 0194 (blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
theorem differential_squared (H : Profinite.{u}ᵒᵖ ⥤ C) (Z : Profinite.{u}) (n : ℕ) :
    differential H Z n ≫ differential H Z (n + 1) = 0 := by
  simpa only [differential_eq] using
    AlgebraicTopology.AlternatingCofaceMapComplex.d_squared ((tuples Z).rightOp ⋙ H) n

/-- Coordinate pullback commutes with the alternating differential. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
theorem coordinate_differential (H : Profinite.{u}ᵒᵖ ⥤ C) {X Y : Profinite.{u}}
    (a : C(X, Y)) (n : ℕ) :
    H.map (coordinate a n).op ≫ differential H X n =
      differential H Y n ≫ H.map (coordinate a (n + 1)).op := by
  simp only [differential, comp_sum, sum_comp, comp_zsmul, zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← H.map_comp, ← H.map_comp, ← op_comp, ← op_comp]
  congr 2

/-- Precomposition of the two vertices commutes with the prism. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
theorem prism_source (H : Profinite.{u}ᵒᵖ ⥤ C) {W X Y : Profinite.{u}}
    (c : C(W, X)) (a b : C(X, Y)) (n : ℕ) :
    prism H a b n ≫ H.map (coordinate c n).op =
      prism H (a.comp c) (b.comp c) n := by
  simp only [prism, sum_comp, zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← H.map_comp, ← op_comp]
  congr 2

/-- Postcomposition of the two vertices commutes with the prism. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
theorem prism_target (H : Profinite.{u}ᵒᵖ ⥤ C) {X Y Z : Profinite.{u}}
    (a b : C(X, Y)) (c : C(Y, Z)) (n : ℕ) :
    H.map (coordinate c (n + 1)).op ≫ prism H a b n =
      prism H (c.comp a) (c.comp b) n := by
  simp only [prism, comp_sum, comp_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← H.map_comp, ← op_comp]
  congr 2
  ext x j
  change c (if j.val ≤ i.val then a (x (i.predAbove j))
    else b (x (i.predAbove j))) =
    (if j.val ≤ i.val then c (a (x (i.predAbove j))) else c (b (x (i.predAbove j))))
  split_ifs <;> rfl

/-- The degree-zero boundary is the difference of endpoint maps. Source: Stacks 019S
(blueprint: lem-sfb-profinite-vertex-prism-boundary). -/
theorem prism_boundary_zero (H : Profinite.{u}ᵒᵖ ⥤ C) {X Y : Profinite.{u}}
    (a b : C(X, Y)) :
    differential H Y 0 ≫ prism H a b 0 =
      H.map (coordinate b 0).op - H.map (coordinate a 0).op := by
  have h₀ : insertion a b 0 0 ≫ deletion Y 0 0 = coordinate b 0 := by
    ext x j
    fin_cases j
    rfl
  have h₁ : insertion a b 0 0 ≫ deletion Y 0 1 = coordinate a 0 := by
    ext x j
    fin_cases j
    rfl
  simp only [differential, prism, Nat.reduceAdd, Fin.sum_univ_one, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    add_comp, neg_comp, ← H.map_comp, ← op_comp, h₀, h₁, sub_eq_add_neg]

/-- The positive-degree signed vertex-prism cancellation, purely in a preadditive category.
No internal Hom, section evaluation, complex or naturality datum is assumed or produced.
Source: Stacks Project, simplicial.tex, Tag 019S, equation-homotopy-to-homotopy and
its preceding cancellation, contravariant adaptation
(blueprint: lem-sfb-profinite-vertex-prism-boundary).

Proof: expand both compositions into double sums. In the second sum, with insertion
index i and deletion index j, pair j<i with insertion i-1 after deletion j in the
first sum; pair j>i+1 with insertion i after deletion j-1. The inverse pairing sends
(k,r) to (r+1,k) for k≤r and to (r,k+1) for k>r. Functoriality identifies the maps
and their integer signs are opposite. The remaining j=i and j=i+1 terms are
H(t_i)-H(t_(i+1)), where t_i uses a before i and b from i onward. Their finite sum
telescopes to the all-b map minus the all-a map. All the parameter equalities are
coordinatewise identities, valid also for empty parameters and the zero category.
-/
theorem prism_boundary (H : Profinite.{u}ᵒᵖ ⥤ C) {X Y : Profinite.{u}}
    (a b : C(X, Y)) (n : ℕ) :
    prism H a b n ≫ differential H X n +
      differential H Y (n + 1) ≫ prism H a b (n + 1) =
      H.map (coordinate b (n + 1)).op - H.map (coordinate a (n + 1)).op := by sorry

end CategoryTheory.CondensedBar.TupleOperators
