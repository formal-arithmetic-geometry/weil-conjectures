/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.Algebra.Homology.FilteredComplexBoundaryPullback

/-! # The kernel calculation on cycle representatives

Source: Stacks Project, Tag 012K, displayed cycle-boundary formulas.
(blueprint: lem-sp-filtered-complex-representative-kernels)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

private theorem pullback_kernel {X Y W : C} (f : X ⟶ Y) (a : W ⟶ X) :
    (Subobject.pullback a).obj (kernelSubobject f) = kernelSubobject (a ≫ f) := by
  simpa only [comp_zero] using pullback_equalizer f 0 a

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_zero_iff {X A : C} (B Z : Subobject X) (h : B ≤ Z)
    (a : A ⟶ (Z : C)) :
    a ≫ cokernel.π (Subobject.ofLE B Z h) = 0 ↔ B.Factors (a ≫ Z.arrow) := by
  constructor
  · intro ha
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨Abelian.monoLift (Subobject.ofLE B Z h) a ha, ?_⟩
    change Abelian.monoLift (Subobject.ofLE B Z h) a ha ≫ B.arrow = _
    rw [← Subobject.ofLE_arrow h, ← Category.assoc, Abelian.monoLift_comp]
  · intro ha
    obtain ⟨b, hb⟩ := (Subobject.factors_iff _ _).mp ha
    change b ≫ B.arrow = a ≫ Z.arrow at hb
    have hab : a = b ≫ Subobject.ofLE B Z h := by
      apply (cancel_mono Z.arrow).mp
      simpa only [Category.assoc, Subobject.ofLE_arrow] using hb.symm
    rw [hab, Category.assoc, cokernel.condition, comp_zero]

private theorem quotient_kernel_pullback {X : C} (B Z : Subobject X) (h : B ≤ Z) :
    kernelSubobject (cokernel.π (Subobject.ofLE B Z h)) =
      (Subobject.pullback Z.arrow).obj B := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff _ _ _).mpr
    exact (quotient_zero_iff B Z h _).mp (kernelSubobject_arrow_comp _)
  · apply le_kernelSubobject
    apply (quotient_zero_iff B Z h _).mpr
    exact (pullback_factors_iff _ _ _).mp (Subobject.factors_self _)

/-- The two maps out of cycle representatives have the same kernel.
Source: Stacks Project, Tag 012K, displayed formulas for Z_r and B_r.
(blueprint: lem-sp-filtered-complex-representative-kernels)

Proof: The projection square identifies the image of a representative x in T with
its class modulo F^{p+1}. Its homology class vanishes exactly when this class is a
boundary, that is, locally on an epimorphic cover x = dy + f with y in F^{p-r+1}
and f in F^{p+1}. Since x and f belong to F^p, dy belongs to F^p as well. Thus the
kernel is the inverse image in R of the image in the graded piece of
(F^p intersect d(F^{p-r+1})) + F^{p+1}, which is B by definition. Conversely a
representative in that inverse image has precisely this decomposition and maps to
a boundary in T. The kernel of Z → Z/B is B, since B → Z is mono in an abelian
category. Pulling it back along z gives the same subobject of R. The epimorphic
covers here express the usual image and sum subobject universal properties, and
the two inclusions descend, so the calculation is valid without assuming C is a
concrete category. -/
theorem filteredComplex_representative_kernels (F : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r)
    (hBZ : F.complexBoundaries p n r ≤ F.complexCycles p n r)
    (ha : p - r + 1 ≤ p) (hb : p + 1 ≤ p + r) :
    let hs := (Int.le_add_one (show p ≤ p from le_rfl)).trans hb
    let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
    let R := F.complexCycleRepresentatives p n r
    let Z := F.complexCycles p n r
    let B := F.complexBoundaries p n r
    let S := F.complexQuotient p (p + r) hs
    let T := F.complexQuotient (p - r + 1) (p + 1) ht
    ∀ (φ : S ⟶ T),
      F.complexQuotientπ p (p + r) hs ≫ φ =
        Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha) ≫
          F.complexQuotientπ (p - r + 1) (p + 1) ht →
      ∀ (z : (R : C) ⟶ (Z : C)) (g : (R : C) ⟶ S.cycles n),
        z ≫ Z.arrow = R.arrow ≫
          (F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n →
        g ≫ S.iCycles n = R.arrow ≫ (F.complexQuotientπ p (p + r) hs).f n →
        kernelSubobject (z ≫ cokernel.π (Subobject.ofLE B Z hBZ)) =
          kernelSubobject (g ≫ S.homologyπ n ≫ HomologicalComplex.homologyMap φ n) := by
  dsimp only
  intro φ hφ z g hz hg
  have ha' : p - r + 1 ≤ p := by
    have h := sub_le_sub_left hr p
    omega
  let R := F.complexCycleRepresentatives p n r
  let S := F.complexQuotient p (p + r)
    ((Int.le_add_one (show p ≤ p from le_rfl)).trans hb)
  let T := F.complexQuotient (p - r + 1) (p + 1)
    (ha.trans (Int.le_add_one (show p ≤ p from le_rfl)))
  have hφn := congrArg (fun f => f.f n) hφ
  have hrep : g ≫ HomologicalComplex.cyclesMap φ n ≫ T.iCycles n =
      R.arrow ≫
        (Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha)).f n ≫
        (F.complexQuotientπ (p - r + 1) (p + 1)
          (ha.trans (Int.le_add_one (show p ≤ p from le_rfl)))).f n := by
    rw [HomologicalComplex.cyclesMap_i, ← Category.assoc, hg, Category.assoc]
    exact congrArg (fun f => R.arrow ≫ f) hφn
  calc
    kernelSubobject (z ≫ cokernel.π
        (Subobject.ofLE (F.complexBoundaries p n r) (F.complexCycles p n r) hBZ)) =
        (Subobject.pullback z).obj ((Subobject.pullback
          (F.complexCycles p n r).arrow).obj (F.complexBoundaries p n r)) := by
      rw [← pullback_kernel, quotient_kernel_pullback]
    _ = (Subobject.pullback (R.arrow ≫
        (F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n)).obj
        (F.complexBoundaries p n r) := by
      rw [← Subobject.pullback_comp, hz]
    _ = (Subobject.pullback R.arrow).obj ((Subobject.pullback
        ((Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha)).f n ≫
          (F.complexQuotientπ (p - r + 1) (p + 1)
            (ha.trans (Int.le_add_one (show p ≤ p from le_rfl)))).f n)).obj
        (kernelSubobject (T.pOpcycles n))) := by
      rw [Subobject.pullback_comp, filteredComplex_boundary_pullback F p n r ha']
    _ = kernelSubobject (g ≫ S.homologyπ n ≫ HomologicalComplex.homologyMap φ n) := by
      rw [← Subobject.pullback_comp, pullback_kernel]
      rw [← kernelSubobject_comp_mono
        (g ≫ S.homologyπ n ≫ HomologicalComplex.homologyMap φ n) (T.homologyι n)]
      congr 1
      rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
      change _ = (g ≫ HomologicalComplex.cyclesMap φ n ≫ T.homologyπ n) ≫ T.homologyι n
      simp only [Category.assoc]
      rw [HomologicalComplex.homology_π_ι]
      simpa only [Category.assoc] using
        (congrArg (fun f => f ≫ T.pOpcycles n) hrep).symm

end CategoryTheory.DecreasingFiltration
