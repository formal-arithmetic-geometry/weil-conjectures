/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationComparisonGraded

/-! # Finite twisting totalization: comparison

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (blueprint: lem-trf-finite-filtered-totalization-comparison). The filtered
map between realizations induced by strictly compatible quasi-isomorphisms.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

set_option maxHeartbeats 1000000 in
-- The summand-by-summand chain-map calculation exceeds the default heartbeat budget.
omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Strictly compatible quasi-isomorphisms of twisting families induce the filtered
comparison map of any two realizations, with graded maps the given ones.
This is the comparison part of the finite twisting assembly.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (step 4 of lem-trf-filtered-mapping-cylinder-step).

Proof:
1. Put `φ^n = (M.coordinates n).hom ≫ biproduct.map (fun p ↦ (f p).f n) ≫
   (M'.coordinates n).inv`; the coordinate equation holds by `biproduct.ι_map`.
2. `φ` is a chain map: compare the summand components of `d_{P'} φ` and `φ d_P` by the
   `differential` fields of `M` and `M'`. The diagonal components agree because each
   `f p` is a chain map; the components `p < q` are `τ'_pq f_p` and `f_q τ_pq`, equal by
   `hτ`; there are no others (def-weil-abstract-derived-category).
3. `φ` maps every tail into the corresponding tail: by `tailInclusion` both tails are
   the inclusions of the summands of weight `≥ r`, and `φ` preserves each summand.
   This gives the `FilteredObject.Hom` (def-sp-filtration).
4. For `p ∈ [a,b]`, both sides of the graded equation are determined after the epi
   `complexQuotientπ` (a cokernel, degreewise); by `gradedProjection` of `M` and `M'`,
   the defining property of `gradedMapSteps` and step 1, both composites equal the
   weight-`p` projection followed by `f p` (def-sp-filtered-complex-subquotients).
5. Hence `gradedMapSteps φ p` is `f p` up to the graded isomorphisms, a
   quasi-isomorphism by `hf`; for `p ∉ [a,b]` both graded pieces are zero (`outside`),
   and a map between zero complexes is a quasi-isomorphism.
(blueprint: lem-trf-finite-filtered-totalization-comparison) -/
theorem exists_finiteTwistingTotalization_comparison
    (D D' : FiniteTwistingFamily R a b)
    (M : FiniteTwistingTotalization D) (M' : FiniteTwistingTotalization D')
    (f : ∀ p : ↥(Finset.Icc a b), D.G p ⟶ D'.G p)
    (hf : ∀ p : ↥(Finset.Icc a b), QuasiIso (f p))
    (hτ : ∀ (p q : ↥(Finset.Icc a b)) (hpq : p.val < q.val) (n : ℤ),
      D.τ p q hpq n ≫ (f q).f (n + 1) = (f p).f n ≫ D'.τ p q hpq n) :
    ∃ φ : FilteredObject.Hom ⟨M.P, M.F⟩ ⟨M'.P, M'.F⟩,
      (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
            (M.coordinates n).inv ≫ φ.hom.f n =
          (f p).f n ≫
            biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p ≫
              (M'.coordinates n).inv) ∧
      (∀ p : ↥(Finset.Icc a b),
        (M.gradedIso p).hom ≫ f p =
          FilteredObject.gradedMapSteps φ p.val ≫ (M'.gradedIso p).hom) ∧
      (∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps φ p)) := by
  classical
  let B : ∀ n : ℤ, (⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n) ⟶
      (⨁ fun p : ↥(Finset.Icc a b) ↦ (D'.G p).X n) :=
    fun n ↦ biproduct.map (fun p ↦ (f p).f n)
  let g : ∀ n : ℤ, M.P.X n ⟶ M'.P.X n :=
    fun n ↦ (M.coordinates n).hom ≫ B n ≫ (M'.coordinates n).inv
  have hg (n : ℤ) : g n ≫ M'.P.d n (n + 1) = M.P.d n (n + 1) ≫ g (n + 1) := by
    dsimp [g]
    apply (cancel_epi (M.coordinates n).inv).1
    apply (cancel_mono (M'.coordinates (n + 1)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
      Category.comp_id]
    apply biproduct.hom_ext'
    intro p
    apply biproduct.hom_ext
    intro q
    dsimp [B]
    rw [← Category.assoc (biproduct.ι _ p) (biproduct.map _)]
    rw [biproduct.ι_map]
    simp only [Category.assoc]
    rw [biproduct.map_π]
    have hd' := congrArg (fun k ↦ (f p).f n ≫ k ≫
        (M'.coordinates (n + 1)).hom ≫ biproduct.π
          (fun p : ↥(Finset.Icc a b) ↦ (D'.G p).X (n + 1)) q)
      (M'.differential p n)
    have hd := congrArg (fun k ↦ k ≫ (M.coordinates (n + 1)).hom ≫
        biproduct.π (fun p : ↥(Finset.Icc a b) ↦ (D.G p).X (n + 1)) q ≫
          (f q).f (n + 1)) (M.differential p n)
    simp only [Category.assoc] at hd' hd
    rw [hd', hd]
    simp only [Category.assoc, Preadditive.add_comp, Preadditive.comp_add,
      Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.comp_sum, biproduct.ι_π]
    by_cases hpq : p = q
    · subst q
      split_ifs with h
      · simp only [eqToHom_refl, Category.comp_id]
        rw [biproduct.ι_π_self_assoc]
        rw [← HomologicalComplex.Hom.comm (f p) n (n + 1)]
        have hL : (∑ j : {q : ↥(Finset.Icc a b) // p.val < q.val},
            (f p).f n ≫ D'.τ p j.val j.property n ≫
              if h : j.val = p then eqToHom (by rw [h]) else 0) = 0 := by
          apply Fintype.sum_eq_zero
          intro j
          have hjp : j.val ≠ p := by
            intro h
            have hh : p.val < p.val := by simpa [h] using j.property
            exact (lt_irrefl _ hh)
          rw [dif_neg hjp, comp_zero]
          simp
        have hR : (∑ x : {q : ↥(Finset.Icc a b) // p.val < q.val},
            D.τ p x.val x.property n ≫
              biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) x.val ≫
              biproduct.π (fun p : ↥(Finset.Icc a b) ↦ (D.G p).X (n + 1)) p ≫
              (f p).f (n + 1)) = 0 := by
          apply Fintype.sum_eq_zero
          intro x
          have hxp : x.val ≠ p := by
            intro h
            have hh : p.val < p.val := by simpa [h] using x.property
            exact (lt_irrefl _ hh)
          rw [biproduct.ι_π_ne_assoc _ hxp]
          simp
        rw [hL, hR]
      · contradiction
    · by_cases hpq' : p.val < q.val
      · let j : {q : ↥(Finset.Icc a b) // p.val < q.val} := ⟨q, hpq'⟩
        simp only [dif_neg hpq, comp_zero]
        rw [biproduct.ι_π_ne_assoc _ hpq]
        rw [Fintype.sum_eq_single j]
        · rw [Fintype.sum_eq_single j]
          · have hjq : (j : ↥(Finset.Icc a b)) = q := Subtype.ext rfl
            rw [dif_pos hjq]
            simp only [eqToHom_refl, Category.comp_id]
            simpa [j] using (hτ p q hpq' n).symm
          · intro j' hj'
            have hjq : (j' : ↥(Finset.Icc a b)) ≠ q := by
              intro he
              apply hj'
              apply Subtype.ext
              exact he
            simp only [biproduct.ι_π_ne_assoc _ hjq, zero_comp, comp_zero]
        · intro j' hj'
          have hjq : (j' : ↥(Finset.Icc a b)) ≠ q := by
            intro he
            apply hj'
            apply Subtype.ext
            exact he
          simp only [dif_neg hjq, comp_zero]
      · simp only [dif_neg hpq, comp_zero]
        rw [biproduct.ι_π_ne_assoc _ hpq]
        have hL : (∑ j : {q : ↥(Finset.Icc a b) // p.val < q.val},
            (f p).f n ≫ D'.τ p j.val j.property n ≫
              if h : j.val = q then eqToHom (by rw [h]) else 0) = 0 := by
          apply Fintype.sum_eq_zero
          intro j
          have hjq : j.val ≠ q := by
            intro he
            exact hpq' (by simpa [he] using j.property)
          rw [dif_neg hjq]
          simp only [comp_zero]
        have hR : (∑ x : {q : ↥(Finset.Icc a b) // p.val < q.val},
            D.τ p x.val x.property n ≫
              biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) x.val ≫
              biproduct.π (fun p : ↥(Finset.Icc a b) ↦ (D.G p).X (n + 1)) q ≫
              (f q).f (n + 1)) = 0 := by
          apply Fintype.sum_eq_zero
          intro x
          have hxq : x.val ≠ q := by
            intro he
            exact hpq' (by simpa [he] using x.property)
          simp only [biproduct.ι_π_ne_assoc _ hxq, zero_comp, comp_zero]
        rw [hL, hR]
        simp
  let φhom : M.P ⟶ M'.P :=
    { f := g
      comm' := by
        intro n m hnm
        subst hnm
        exact hg n }
  have hcoord : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
            (M.coordinates n).inv ≫ φhom.f n =
          (f p).f n ≫ biproduct.ι
            (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p ≫
            (M'.coordinates n).inv := by
      intro p n
      simp only [φhom, g, B]
      simp
  obtain ⟨ψ, hψ⟩ := exists_finiteTwistingTotalization_comparison_hom
    D D' M M' f φhom hcoord
  obtain ⟨hgrade, hqi⟩ := exists_finiteTwistingTotalization_comparison_graded
    D D' M M' f hf ψ hψ
  exact ⟨ψ, hψ, hgrade, hqi⟩

end CochainComplex
