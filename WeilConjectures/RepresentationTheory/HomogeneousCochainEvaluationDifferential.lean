/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RepresentationTheory.HomogeneousCochainEvaluation

/-!
# The differential in cumulative-product coordinates

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential.
-/

@[expose] public section

universe u s

namespace Rep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem resolutionEval_d (N : TopRep.{max u s} ℤ G) (n : ℕ)
    (x : (TopRep.resolutionX N n).V) (g : Fin (n + 1) → G) :
    resolutionEval N (n + 1) ((TopRep.d N n).hom x) g =
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
        resolutionEval N n x (g ∘ i.succAbove) := by
  induction n with
  | zero => simp [resolutionEval, TopRep.d_zero]
  | succ n ih =>
    change resolutionEval N (n + 1) (((TopRep.d N (n + 1)).hom x) (g 0))
      (Fin.tail g) = _
    rw [TopRep.hom_d_succ]
    change resolutionEval N (n + 1) (x - (TopRep.d N n).hom (x (g 0)))
      (Fin.tail g) = _
    rw [show resolutionEval N (n + 1) (x - (TopRep.d N n).hom (x (g 0)))
        (Fin.tail g) = resolutionEval N (n + 1) x (Fin.tail g) -
          resolutionEval N (n + 1) ((TopRep.d N n).hom (x (g 0))) (Fin.tail g)
      from congrFun ((resolutionEval N (n + 1)).map_sub _ _) (Fin.tail g)]
    rw [ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Function.comp_def]
    rw [sub_eq_add_neg]
    apply congrArg (resolutionEval N (n + 1) x (Fin.tail g) + ·)
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have ht : (fun j ↦ Fin.tail g (i.succAbove j)) =
        Fin.tail (fun j ↦ g (i.succ.succAbove j)) := by
      funext j
      change g (i.succAbove j).succ = g (i.succ.succAbove j.succ)
      rw [Fin.succ_succAbove_succ]
    simp [resolutionEval, pow_succ, ht]

/-- Evaluation of the recursive homogeneous differential gives the inhomogeneous formula.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential. -/
theorem homogeneousCochainEvaluation_differential [CompactSpace G] [T2Space G]
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (n : ℕ) (x : (TopRep.homogeneousCochains N).X n) (g : Fin (n + 1) → G) :
    homogeneousCochainEvaluation N (n + 1)
        (((TopRep.homogeneousCochains N).d n (n + 1)).hom x) g =
      N.ρ (g 0) (homogeneousCochainEvaluation N n x (fun k ↦ g k.succ)) +
        ∑ k : Fin (n + 1),
          (-1 : ℤ) ^ (k.val + 1) •
            homogeneousCochainEvaluation N n x (Fin.contractNth k (· * ·) g) := by
  change resolutionEval N (n + 2)
      (((TopRep.homogeneousCochains N).d n (n + 1)).hom x).val (Fin.partialProd g) =
    N.ρ (g 0) (resolutionEval N (n + 1) x.val (Fin.partialProd (Fin.tail g))) +
      ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k.val + 1) •
        resolutionEval N (n + 1) x.val (Fin.partialProd (Fin.contractNth k (· * ·) g))
  rw [TopRep.homogeneousCochains.d_apply, resolutionEval_d, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  have hfirst : Fin.partialProd g ∘ (0 : Fin (n + 2)).succAbove =
      fun i ↦ g 0 * Fin.partialProd (Fin.tail g) i := by
    funext i
    simp [Fin.partialProd_succ']
  rw [hfirst, resolutionEval_equivariant]
  apply congrArg (N.ρ (g 0)
    (resolutionEval N (n + 1) x.val (Fin.partialProd (Fin.tail g))) + ·)
  apply Finset.sum_congr rfl
  intro k _
  rw [← Fin.partialProd_contractNth]

end Rep
