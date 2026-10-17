/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexDecalagePageData
import all Sheaf.Algebra.Homology.FilteredComplexBoundaryPullback

/-! # Covering cycles in the left decalage interval

Source: Stacks Project, Tags 012K and 015X.
(blueprint: lem-sp-filtered-complex-decalage-left-representatives).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Original r-cycle representatives cover the cycles of the left decalage interval.
Source: Stacks Project, Tag 012K, cycle formula; Tag 015X, second filtration.
(blueprint: lem-sp-filtered-complex-decalage-left-representatives).

Proof. The differential of a representative belongs to the upper decalage step:
its filtration index there is p+r, and its next differential is zero. Thus its
projection is a cycle. To cover an arbitrary quotient cycle, lift it degreewise
along the epic quotient projection. Its differential lifts to the upper step by
exactness after an epimorphic refinement. The lower decalage condition places the
lift in F^p; the upper step places its differential in F^(p+r). It therefore
factors through the original representative pullback. Cancel the monic cycle
inclusion to verify the lift equation and apply the refinement criterion for epis. -/
theorem filteredComplexDecalageLeftRepresentatives
    (U : FilteredObject (CochainComplex C ℤ)) (p q r : ℤ) (hr : 2 ≤ r)
    (a b : ℤ) (ha : a + (p + q) = p) (hb : b + (p + q + 1) = p + r)
    (k : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶
      (U.filtration.decalage.step a : CochainComplex C ℤ).X (p + q))
    (hk : k ≫ (U.filtration.decalage.step a).arrow.f (p + q) =
      (U.filtration.complexCycleRepresentatives p (p + q) r).arrow ≫
        (U.filtration.step p).arrow.f (p + q)) :
    let Q := U.filtration.decalage.complexQuotient a b (by omega)
    ∃ g : (U.filtration.complexCycleRepresentatives p (p + q) r : C) ⟶ Q.cycles (p + q),
      Epi g ∧ g ≫ Q.iCycles (p + q) =
        k ≫ (U.filtration.decalage.complexQuotientπ a b (by omega)).f (p + q) := by
  dsimp only
  let F := U.filtration
  let D := F.decalage
  let n := p + q
  let A : CochainComplex C ℤ := D.step a
  let B : CochainComplex C ℤ := D.step b
  let Q := D.complexQuotient a b (by omega)
  let π := D.complexQuotientπ a b (by omega)
  let l := Subobject.ofLE (D.step b) (D.step a) (D.antitone_step (by omega))
  let R := F.complexCycleRepresentatives p n r
  have hD (a m : ℤ) : D.complexStep a m ≤ F.complexStep (a + m) m := by
    rw [DecreasingFiltration.decalage_complexStep]
    exact inf_le_left
  have hd : (D.complexStep b (n + 1)).Factors
      (R.arrow ≫ (F.step p).arrow.f n ≫ U.obj.d n (n + 1)) := by
    rw [DecreasingFiltration.decalage_complexStep]
    have hb' : b + (n + 1) = p + r := hb
    rw [hb']
    apply (Subobject.inf_factors _).mpr
    constructor
    · have hf := (pullback_factors_iff _ _ _).mp R.factors_self
      have h := (pullback_factors_iff _ _ _).mp (Subobject.factors_right_of_inf_factors hf)
      simpa only [Category.assoc] using h
    · apply (pullback_factors_iff _ _ _).mpr
      simp only [Category.assoc, U.obj.d_comp_d, comp_zero]
      exact Subobject.factors_zero
  rw [DecreasingFiltration.complexStep, imageSubobject_mono,
    Subobject.mk_factors_iff] at hd
  obtain ⟨y, hy⟩ : ∃ y : (R : C) ⟶ B.X (n + 1),
      y ≫ (D.step b).arrow.f (n + 1) =
        R.arrow ≫ (F.step p).arrow.f n ≫ U.obj.d n (n + 1) := hd
  have hdy : k ≫ A.d n (n + 1) = y ≫ l.f (n + 1) := by
    apply (cancel_mono ((D.step a).arrow.f (n + 1))).1
    rw [Category.assoc, ← (D.step a).arrow.comm, ← Category.assoc, hk]
    simpa only [A, B, l, Category.assoc, ← HomologicalComplex.comp_f,
      Subobject.ofLE_arrow] using hy.symm
  have hcycle : (k ≫ π.f n) ≫ Q.d n (n + 1) = 0 := by
    rw [Category.assoc, π.comm, ← Category.assoc, hdy]
    simp only [Category.assoc, π, l, DecreasingFiltration.complexQuotientπ,
      ← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f, comp_zero]
  let g := HomologicalComplex.liftCycles Q (k ≫ π.f n) (n + 1) (by simp) hcycle
  have hg : g ≫ Q.iCycles n = k ≫ π.f n := HomologicalComplex.liftCycles_i _ _ _ _ _
  refine ⟨g, ?_, hg⟩
  apply (epi_iff_surjective_up_to_refinements g).mpr
  intro X w
  have := DecreasingFiltration.quotient_epi D a b n (by omega)
  obtain ⟨X₁, e₁, he₁, t, ht⟩ := surjective_up_to_refinements_of_epi (π.f n) (w ≫ Q.iCycles n)
  have htzero : (t ≫ A.d n (n + 1)) ≫ π.f (n + 1) = 0 := by
    rw [Category.assoc, ← π.comm, ← Category.assoc, ← ht]
    have hw : (w ≫ Q.iCycles n) ≫ Q.d n (n + 1) = 0 := by
      rw [Category.assoc, Q.iCycles_d, comp_zero]
    simpa only [Category.assoc, comp_zero] using congrArg (fun f ↦ e₁ ≫ f) hw
  obtain ⟨X₂, e₂, he₂, s, hs⟩ :=
    (DecreasingFiltration.quotient_exact D a b (n + 1)
      (by omega)).exact_up_to_refinements (t ≫ A.d n (n + 1)) htzero
  change e₂ ≫ t ≫ A.d n (n + 1) = s ≫ l.f (n + 1) at hs
  let x := e₂ ≫ t ≫ (D.step a).arrow.f n
  have hx : (F.complexStep p n).Factors x := by
    have hh : (D.complexStep a n).Factors x := by
      change (imageSubobject ((D.step a).arrow.f n)).Factors x
      dsimp only [x]
      simpa only [Category.assoc] using
        imageSubobject_factors_comp_self ((D.step a).arrow.f n) (e₂ ≫ t)
    have hDa := hD a n
    rw [ha] at hDa
    exact Subobject.factors_of_le x hDa hh
  have hdx : (F.complexStep (p + r) (n + 1)).Factors (x ≫ U.obj.d n (n + 1)) := by
    have heq : x ≫ U.obj.d n (n + 1) = s ≫ (D.step b).arrow.f (n + 1) := by
      dsimp only [x]
      rw [Category.assoc, Category.assoc, (D.step a).arrow.comm]
      simpa only [A, l, Category.assoc, ← HomologicalComplex.comp_f,
        Subobject.ofLE_arrow] using
          congrArg (fun f ↦ f ≫ (D.step a).arrow.f (n + 1)) hs
    rw [heq]
    have hb' : b + (n + 1) = p + r := hb
    have hDb := hD b (n + 1)
    rw [hb'] at hDb
    apply Subobject.factors_of_le _ hDb
    exact imageSubobject_factors_comp_self _ _
  have hx' := hx
  rw [DecreasingFiltration.complexStep, imageSubobject_mono,
    Subobject.mk_factors_iff] at hx'
  obtain ⟨f, hf⟩ : ∃ f : X₂ ⟶ (F.step p : CochainComplex C ℤ).X n,
      f ≫ (F.step p).arrow.f n = x := hx' 
  have hR : R.Factors f := by
    apply (pullback_factors_iff _ _ _).mpr
    rw [hf]
    exact (Subobject.inf_factors _).mpr ⟨hx, (pullback_factors_iff _ _ _).mpr hdx⟩
  let v := R.factorThru f hR
  have hv : v ≫ k = e₂ ≫ t := by
    apply (cancel_mono ((D.step a).arrow.f n)).1
    rw [Category.assoc, hk, ← Category.assoc, Subobject.factorThru_arrow, hf]
    simp only [x, Category.assoc]
  refine ⟨X₂, e₂ ≫ e₁, inferInstance, v, ?_⟩
  apply (cancel_mono (Q.iCycles n)).1
  simp only [Category.assoc]
  rw [ht, hg]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ π.f n) hv.symm

end CategoryTheory
