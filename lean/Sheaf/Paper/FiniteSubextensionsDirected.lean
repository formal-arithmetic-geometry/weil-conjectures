/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF stage-2 worker Q45
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Finite subextensions of `ℚ̄_ℓ`

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-qlbar-condensed/det-def-sfb-qlbar-condensed-subextensions.md`
(blueprint: det-def-sfb-qlbar-condensed-subextensions).

The finite subextensions of the chosen algebraic closure `PadicAlgCl ℓ` are represented by
`PadicAlgCl.FiniteIntermediateField ℓ`.  The statement records finite composita, their degree
bound, directedness, and the fact that every finite subset of the algebraic closure is contained
in one of these fields.
-/

@[expose] public section

open scoped BigOperators
open PadicAlgCl

namespace PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime]

/--
Let `ℓ` be prime, let `k = ℚ_[ℓ]`, and let `PadicAlgCl ℓ` be the chosen algebraic closure of `k`.
For a finite family of finite intermediate fields, the `iSup` is their compositum (with the
empty compositum equal to `k`), is finite over `k`, contains every member, and has degree at
most the product of their degrees.  These fields are directed under inclusion; every finite
subset of `PadicAlgCl ℓ` lies in one, and the algebraic closure is their union.

The proof follows the blueprint's four steps:
1. Apply `lem-weil-pbc-compositum-degree-bound` to finite intermediate fields `E, F`, giving
   finiteness of their compositum over `E` and relative degree at most `[F : k]`. Then apply
   `lem-weil-pbc-field-degree-multiplicativity` to `k ⊆ E ⊆ EF`: the compositum is finite over
   `k` and its degree is at most `[E : k] * [F : k]`. It contains both fields by definition.
2. Induct on the size of a finite family, using the binary assertion at each successor. For
   the empty family the compositum is the bottom field, of degree one, and the product is
   one. Inclusion inherits a partial order; the bottom field witnesses nonemptiness, and
   binary composita give common upper bounds.
3. By `def-weil-algebraic-closure`, every element of the closure is algebraic over `k`.
   Apply `lem-weil-pbc-algebraic-generators-finite-extension` to each singleton, and take the
   finite compositum supplied by step 2 to contain a given finite subset. For the empty
   subset use the bottom field.
4. Every finite intermediate field lies in the closure. Conversely, step 3 for `{x}` puts
   any element `x` of the closure in such a field. These are the two union inclusions.
No separability, disjointness, or completeness hypothesis is used.
(source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-qlbar-condensed/det-def-sfb-qlbar-condensed-subextensions.md;
(blueprint: det-def-sfb-qlbar-condensed-subextensions))
-/
theorem finiteSubextensions_directed :
    (∀ (n : ℕ) (E : Fin n → FiniteIntermediateField ℓ),
      FiniteDimensional ℚ_[ℓ]
          (iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
            (fun i : Fin n => (E i).1)) ∧
        (∀ i, (E i).1 ≤
          iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (fun j : Fin n => (E j).1)) ∧
        Module.finrank ℚ_[ℓ]
            (iSup (α := IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
              (fun i : Fin n => (E i).1)) ≤
          ∏ i, Module.finrank ℚ_[ℓ] ((E i).1)) ∧
      Nonempty (FiniteIntermediateField ℓ) ∧
      (∀ E F : FiniteIntermediateField ℓ,
        ∃ G : FiniteIntermediateField ℓ, E.1 ≤ G.1 ∧ F.1 ≤ G.1) ∧
      (∀ S : Finset (PadicAlgCl ℓ),
        ∃ E : FiniteIntermediateField ℓ, ∀ x, x ∈ S → x ∈ E.1) ∧
      (∀ x : PadicAlgCl ℓ,
        ∃ E : FiniteIntermediateField ℓ, x ∈ E.1) := by
  classical
  have hfamily : ∀ (n : ℕ) (E : Fin n → FiniteIntermediateField ℓ),
      Module.finrank ℚ_[ℓ]
        (⨆ i, (E i).1 : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) ≤
        ∏ i, Module.finrank ℚ_[ℓ] (E i).1 := by
    intro n
    induction n with
    | zero =>
        intro E
        rw [iSup_of_empty, IntermediateField.finrank_bot]
        simp
    | succ n ih =>
        intro E
        have hs : (⨆ i, (E i).1 : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) =
            (E 0).1 ⊔ ⨆ i : Fin n, (E i.succ).1 := by
          apply le_antisymm
          · refine iSup_le (Fin.cases le_sup_left (fun i ↦ ?_))
            exact (le_iSup (fun j : Fin n ↦ (E j.succ).1) i).trans le_sup_right
          · exact sup_le (le_iSup (fun j ↦ (E j).1) 0)
              (iSup_le fun i ↦ le_iSup (fun j ↦ (E j).1) i.succ)
        rw [hs, Fin.prod_univ_succ]
        exact (IntermediateField.finrank_sup_le _ _).trans
          (Nat.mul_le_mul_left _ (ih (fun i ↦ E i.succ)))
  have hsubset : ∀ S : Finset (PadicAlgCl ℓ),
      ∃ E : FiniteIntermediateField ℓ, ∀ x, x ∈ S → x ∈ E.1 := by
    intro S
    refine ⟨⟨IntermediateField.adjoin ℚ_[ℓ] (S : Set (PadicAlgCl ℓ)), ?_⟩, ?_⟩
    · exact IntermediateField.finiteDimensional_adjoin
        (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
    · intro x hx
      exact IntermediateField.subset_adjoin ℚ_[ℓ] (S : Set (PadicAlgCl ℓ)) hx
  refine ⟨?_, inferInstance, ?_, hsubset, ?_⟩
  · intro n E
    exact ⟨inferInstance, fun i ↦ le_iSup (fun j ↦ (E j).1) i, hfamily n E⟩
  · intro E F
    exact ⟨⟨E.1 ⊔ F.1, inferInstance⟩, le_sup_left, le_sup_right⟩
  · intro x
    obtain ⟨E, hE⟩ := hsubset {x}
    exact ⟨E, hE x (Finset.mem_singleton_self x)⟩

end PadicAlgCl
