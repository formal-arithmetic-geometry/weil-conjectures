/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingPrefixContribution
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingTailContribution

/-!
# Junction deletions in the first sorting homotopy

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM, equation 20.23.6.1.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

open Classical in
/-- The outgoing junction deletions give the successive partial sorting differences.

Source: Stacks 01FM, verification of equation 20.23.6.1 (the computation omitted
in the source), junction terms of the labelled-deletion argument. -/
theorem cechFirstSortingJunctionDeletions (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    (p : ℕ) (s : S.cochains F (p + 1)) (t : Fin (p + 2) → I) :
    let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
        (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
      ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
        F.map (S.indexMap t (cechJunction σ τ a)).op
          ((-1 : ℤ) ^ r.val •
            F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
              (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove)))
    let B : ℕ → S.cochains F (p + 1) := fun a t ↦
      ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ τ : Equiv.Perm (Fin (p + 2)),
        if cechStableSort t σ ∧
            (∀ k, k.val < a → τ k = σ k) ∧
            (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
          (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
    (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r = σ a then E σ a τ r else 0) =
      ∑ a : Fin (p + 2), (B a.val t - B (a.val + 1) t) := by
  classical
  let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
      (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
    ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
      F.map (S.indexMap t (cechJunction σ τ a)).op
        ((-1 : ℤ) ^ r.val •
          F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
            (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove)))
  let P := ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ r.val ≤ a.val then E σ a τ r else 0
  let T := ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r = σ a) ∧ a.val < r.val then E σ a τ r else 0
  let B : ℕ → S.cochains F (p + 1) := fun a t ↦
    ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ τ : Equiv.Perm (Fin (p + 2)),
      if cechStableSort t σ ∧
          (∀ k, k.val < a → τ k = σ k) ∧
          (∀ i j, a ≤ i.val → i < j → τ i < τ j) then
        (Equiv.Perm.sign τ : ℤ) • F.map (S.indexMap t τ).op (s (t ∘ τ)) else 0
  dsimp only
  have hP := cechFirstSortingJunctionPrefixContribution X U F S p s t
  have hT := cechFirstSortingJunctionTailContribution X U F S p s t
  change P = ∑ a : Fin (p + 2), B a.val t at hP
  change T = - ∑ a : Fin (p + 2), B (a.val + 1) t at hT
  have hsplit : (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r = σ a then E σ a τ r else 0) = P + T := by
    dsimp [P, T]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro τ hτ
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : cechJunction σ τ a r = σ a
    · by_cases ha' : r.val ≤ a.val
      · simp [h, ha']
      · have hr' : a.val < r.val := by omega
        simp [h, ha', hr']
    · simp [h]
  rw [hsplit]
  change P + T = ∑ a : Fin (p + 2), (B a.val t - B (a.val + 1) t)
  rw [hP, hT]
  rw [Finset.sum_sub_distrib]
  simp only [sub_eq_add_neg]

end AlgebraicGeometry.Scheme
