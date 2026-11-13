/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSortingOperators
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingPrefixCancellation
import WeilConjectures.AlgebraicGeometry.AlternatingCechFirstSortingTailCancellation

/-!
# Nonjunction cancellation in the first sorting homotopy

## References

* Stacks Project, Tag 01FM
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem sortingRestriction_comp (X : Scheme.{u}) {I : Type v}
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤)))
    {m n k : ℕ} (t : Fin (m + 1) → I) (α : Fin (n + 1) → Fin (m + 1))
    (β : Fin (k + 1) → Fin (n + 1)) (s : S.cochains F k) :
    F.map (S.indexMap t α).op
        (F.map (S.indexMap (t ∘ α) β).op (s ((t ∘ α) ∘ β))) =
      F.map (S.indexMap t (α ∘ β)).op (s (t ∘ (α ∘ β))) := by
  have hm : (S.indexMap t (α ∘ β)).op =
      (S.indexMap (t ∘ α) β).op ≫ (S.indexMap t α).op := Subsingleton.elim _ _
  rw [hm, F.map_comp]
  rfl

open Classical in
/-- Outgoing nonjunction deletions cancel the incoming differential expansion (Stacks, Tag 01FM). -/
theorem cechFirstSortingNonjunctionCancellation (X : Scheme.{u}) {I : Type v} [LinearOrder I]
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
    (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r ≠ σ a then E σ a τ r else 0) +
      (S.differential F p (cechFirstSortingHom X U F S p s)) t = 0 := by
  classical
  let V := fun (α : Fin (p + 2) → Fin (p + 2)) ↦
    F.map (S.indexMap t α).op (s (t ∘ α))
  let E := fun (σ : Equiv.Perm (Fin (p + 2))) (a : Fin (p + 2))
      (τ : Equiv.Perm (Fin (p + 2))) (r : Fin (p + 3)) ↦
    (((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) * (-1 : ℤ) ^ r.val) •
      V (cechJunction σ τ a ∘ r.succAbove)
  let D := fun (j : Fin (p + 2)) (σ : Equiv.Perm (Fin (p + 1)))
      (b : Fin (p + 1)) (τ : Equiv.Perm (Fin (p + 1))) ↦
    ((-1 : ℤ) ^ j.val * ((-1 : ℤ) ^ b.val * (Equiv.Perm.sign τ : ℤ))) •
      V (j.succAbove ∘ cechJunction σ τ b)
  let before := fun (j : Fin (p + 2)) (σ : Equiv.Perm (Fin (p + 1)))
      (b : Fin (p + 1)) ↦
    t j < t (j.succAbove (σ b)) ∨
      (t j = t (j.succAbove (σ b)) ∧ j < j.succAbove (σ b))
  let N := ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r ≠ σ a then E σ a τ r else 0
  let NP := ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r ≠ σ a) ∧ r.val < a.val then E σ a τ r else 0
  let NT := ∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
    ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
      if ((cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
          cechJunction σ τ a r ≠ σ a) ∧ ¬ r.val < a.val then E σ a τ r else 0
  let DI := ∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)),
    ∑ b : Fin (p + 1), ∑ τ : Equiv.Perm (Fin (p + 1)),
      if cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b then
        D j σ b τ else 0
  let DP := ∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)),
    ∑ b : Fin (p + 1), ∑ τ : Equiv.Perm (Fin (p + 1)),
      if (cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b) ∧
          before j σ b then D j σ b τ else 0
  let DT := ∑ j : Fin (p + 2), ∑ σ : Equiv.Perm (Fin (p + 1)),
    ∑ b : Fin (p + 1), ∑ τ : Equiv.Perm (Fin (p + 1)),
      if (cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b) ∧
          ¬ before j σ b then D j σ b τ else 0
  have hP : NP + DP = 0 := cechFirstSortingPrefixCancellation p t V
  have hT : NT + DT = 0 := cechFirstSortingTailCancellation p t V
  have hN : N = NP + NT := by
    dsimp only [N, NP, NT]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro τ _
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
        cechJunction σ τ a r ≠ σ a
    · by_cases hr : r.val < a.val <;> simp [h, hr]
    · simp [h]
  have hD : DI = DP + DT := by
    dsimp only [DI, DP, DT]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases h : cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b
    · by_cases hb : before j σ b <;> simp [h, hb]
    · simp [h]
  have hd : (S.differential F p (cechFirstSortingHom X U F S p s)) t = DI := by
    change (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      F.map (S.indexMap t j.succAbove).op
        (∑ σ : Equiv.Perm (Fin (p + 1)), ∑ b : Fin (p + 1),
          ∑ τ : Equiv.Perm (Fin (p + 1)),
            if cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b then
              ((-1 : ℤ) ^ b.val * (Equiv.Perm.sign τ : ℤ)) •
                F.map (S.indexMap (t ∘ j.succAbove) (cechJunction σ τ b)).op
                  (s ((t ∘ j.succAbove) ∘ cechJunction σ τ b)) else 0)) = DI
    dsimp only [DI, D, V]
    simp only [map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases h : cechStableSort (t ∘ j.succAbove) σ ∧ cechPartialSort σ τ b
    · simp only [h, and_self, ite_true, map_zsmul, smul_smul]
      rw [sortingRestriction_comp X U F S]
    · simp [h]
  have hn : (∑ σ : Equiv.Perm (Fin (p + 2)), ∑ a : Fin (p + 2),
      ∑ τ : Equiv.Perm (Fin (p + 2)), ∑ r : Fin (p + 3),
        if (cechStableSort t σ ∧ cechPartialSort σ τ a) ∧
            cechJunction σ τ a r ≠ σ a then
          ((-1 : ℤ) ^ a.val * (Equiv.Perm.sign τ : ℤ)) •
            F.map (S.indexMap t (cechJunction σ τ a)).op
              ((-1 : ℤ) ^ r.val •
                F.map (S.indexMap (t ∘ cechJunction σ τ a) r.succAbove).op
                  (s ((t ∘ cechJunction σ τ a) ∘ r.succAbove))) else 0) = N := by
    dsimp only [N, E, V]
    simp only [map_zsmul, sortingRestriction_comp X U F S, smul_smul]
  dsimp only
  rw [hn, hd, hN, hD]
  calc
    (NP + NT) + (DP + DT) = (NP + DP) + (NT + DT) := by abel
    _ = 0 := by rw [hP, hT, add_zero]


end AlgebraicGeometry.Scheme
