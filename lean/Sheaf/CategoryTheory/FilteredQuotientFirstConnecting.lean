/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
/-!
# The first quotient-page differential as a connecting map

Source: Stacks Project, Tag 012K, Lemma 12.24.3(1).
(blueprint: lem-sp-filtered-quotient-first-connecting).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem quotient_sequence
    {A : Type u} [Category.{v} A] [Abelian A] {X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] (h : X ⟶ Z) (hfg : f ≫ g = h) :
    ∃ (i : cokernel f ⟶ cokernel h) (j : cokernel h ⟶ cokernel g)
      (hij : i ≫ j = 0), (ShortComplex.mk i j hij).ShortExact ∧
      cokernel.π f ≫ i = g ≫ cokernel.π h ∧ cokernel.π h ≫ j = cokernel.π g := by
  subst h
  let S := kernelCokernelCompSequence.snakeInput f g
  have hm : Mono S.L₃.f := by
    apply (S.L₂'.exact_iff_mono ?_).mp S.L₂'_exact
    exact (isZero_kernel_of_mono g).eq_of_src _ _
  have he : Epi S.L₃.g := by
    dsimp [S, kernelCokernelCompSequence.snakeInput]
    infer_instance
  refine ⟨S.L₃.f, S.L₃.g, S.L₃.zero, ⟨S.L₃_exact⟩, ?_, ?_⟩
  · simp [S, kernelCokernelCompSequence.snakeInput]
  · simp [S, kernelCokernelCompSequence.snakeInput]

private theorem filtered_quotient_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K)
    (p b : ℤ) (hb : p + 1 + 1 = b) :
    ∃ (i : F.gradedPiece (p + 1) ⟶ F.complexQuotient p b (by omega))
      (j : F.complexQuotient p b (by omega) ⟶ F.gradedPiece p)
      (hij : i ≫ j = 0) (_hS : (ShortComplex.mk i j hij).ShortExact),
      F.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
        Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega)) ≫
          F.complexQuotientπ p b (by omega) ∧
      F.complexQuotientπ p b (by omega) ≫ j =
        F.complexQuotientπ p (p + 1) (by omega) := by
  subst b
  let f := Subobject.ofLE (F.step (p + 1 + 1)) (F.step (p + 1))
    (F.antitone_step (by omega))
  let g := Subobject.ofLE (F.step (p + 1)) (F.step p)
    (F.antitone_step (by omega))
  let h := Subobject.ofLE (F.step (p + 1 + 1)) (F.step p)
    (F.antitone_step (by omega))
  have hfg : f ≫ g = h := Subobject.ofLE_comp_ofLE _ _ _ _ _
  obtain ⟨i, j, hij, hS, hi, hj⟩ := quotient_sequence f g h hfg
  exact ⟨i, j, hij, hS, hi, hj⟩

private theorem representative_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (p n n' : ℤ) (hn : n + 1 = n')
    {A : C} (t : A ⟶ (F.step p : CochainComplex C ℤ).X n)
    (ht : (F.complexStep (p + 1) n').Factors
      (t ≫ (F.step p).arrow.f n ≫ K.d n n')) :
    (F.complexCycleRepresentatives p n 1).Factors t := by
  subst n'
  apply (pullback_factors_iff _ _ _).mpr
  apply (Subobject.inf_factors _).mpr
  exact ⟨imageSubobject_factors_comp_self _ _,
    (pullback_factors_iff _ _ _).mpr (by simpa only [Category.assoc] using ht)⟩

private theorem representative_normalization
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} (F : DecreasingFiltration K) (p n : ℤ)
    {Q : C} (π : (F.complexCycles p n 1 : C) ⟶ Q)
    (e : Q ⟶ (F.gradedPiece p).homology n)
    (z : (F.complexCycleRepresentatives p n 1 : C) ⟶ (F.complexCycles p n 1 : C))
    (g : (F.complexCycleRepresentatives p n 1 : C) ⟶ (F.gradedPiece p).cycles n)
    (hz : z ≫ (F.complexCycles p n 1).arrow =
      (F.complexCycleRepresentatives p n 1).arrow ≫
        (F.complexQuotientπ p (p + 1) (by omega)).f n)
    (hg : g ≫ (F.gradedPiece p).iCycles n =
      (F.complexCycleRepresentatives p n 1).arrow ≫
        (F.complexQuotientπ p (p + 1) (by omega)).f n)
    (he : z ≫ π ≫ e = g ≫ (F.gradedPiece p).homologyπ n)
    {A : C} (t : A ⟶ (F.step p : CochainComplex C ℤ).X n)
    (ht : (F.complexCycleRepresentatives p n 1).Factors t)
    (x : A ⟶ (F.complexCycles p n 1 : C))
    (y : A ⟶ (F.gradedPiece p).cycles n)
    (hx : x ≫ (F.complexCycles p n 1).arrow =
      t ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n)
    (hy : y ≫ (F.gradedPiece p).iCycles n =
      t ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n) :
    x ≫ π ≫ e = y ≫ (F.gradedPiece p).homologyπ n := by
  let a := Subobject.factorThru _ t ht
  have ha : a ≫ (F.complexCycleRepresentatives p n 1).arrow = t := by simp [a]
  have hx' : x = a ≫ z := by
    apply (cancel_mono (F.complexCycles p n 1).arrow).1
    rw [hx, Category.assoc, hz, ← Category.assoc, ha]
  have hy' : y = a ≫ g := by
    apply (cancel_mono ((F.gradedPiece p).iCycles n)).1
    rw [hy, Category.assoc, hg, ← Category.assoc, ha]
  rw [hx', hy', Category.assoc, he, Category.assoc]

private theorem connecting_representative
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (n m : ℤ) (hn : (ComplexShape.up ℤ).Rel n m)
    {A : C} (a : A ⟶ S.X₃.cycles n) (b : A ⟶ S.X₂.X n)
    (c : A ⟶ S.X₁.cycles m)
    (hb : b ≫ S.g.f n = a ≫ S.X₃.iCycles n)
    (hc : c ≫ S.X₁.iCycles m ≫ S.f.f m = b ≫ S.X₂.d n m) :
    a ≫ S.X₃.homologyπ n ≫ hS.δ n m hn = c ≫ S.X₁.homologyπ m := by
  rw [← Category.assoc]
  apply hS.δ_eq' n m hn (a ≫ S.X₃.homologyπ n) (b ≫ S.X₂.pOpcycles n) c
  · simp only [Category.assoc, HomologicalComplex.p_opcyclesMap,
      HomologicalComplex.homology_π_ι]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ S.X₃.pOpcycles n) hb
  · apply (cancel_mono (S.X₂.iCycles m)).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.opcyclesToCycles_iCycles,
      HomologicalComplex.p_fromOpcycles]
    exact hc

set_option linter.unusedVariables false in
/-- The representative differential on the first concrete quotient page is the
connecting homomorphism of the two-step filtration quotient sequence.
Source: Stacks Project, Tag 012K, Lemma 12.24.3(1).
(blueprint: lem-sp-filtered-quotient-first-connecting).

Proof. The cokernel universal properties for the inclusions F^(p+2) into
F^(p+1) into F^p construct i and j with the displayed projection squares.
The quotient-of-quotients exact sequence makes this sequence short exact.
Lift a first-page cycle representative in F^p to F^p/F^(p+2). Its differential
lies in F^(p+1), and its image in gr^(p+1) is a cycle. The homology connecting
map sends the original graded cycle to this differentiated cycle, by the
connecting-map representative formula. The two equations in hH identify
the original and differentiated quotient classes with these homology classes.
Precompose with the epic representative projection followed by the epic
boundary cokernel projection. The on_representatives equation of D then
makes both sides identical; cancellation of this epic composite proves the
stated equality. This calculation uses only one page, not a spectral sequence. -/
theorem filteredQuotient_first_connecting
    (C : Type u) [Category.{v} C] [Abelian C]
    (hBZ : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
      (p q r : ℤ) (hr : 1 ≤ r),
      U.obj.filtration.complexBoundaries p (p + q) r ≤
        U.obj.filtration.complexCycles p (p + q) r)
    (eH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      cokernel (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≅
        (U.obj.filtration.gradedPiece p).homology (p + q))
    (hH : ∀ (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)) (p q : ℤ),
      ∃ (z : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.complexCycles p (p + q) 1 : C))
        (g : (U.obj.filtration.complexCycleRepresentatives p (p + q) 1 : C) ⟶
          (U.obj.filtration.gradedPiece p).cycles (p + q)),
        z ≫ (U.obj.filtration.complexCycles p (p + q) 1).arrow =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        g ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
          (U.obj.filtration.complexCycleRepresentatives p (p + q) 1).arrow ≫
            (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q) ∧
        Epi z ∧
        z ≫ cokernel.π (Subobject.ofLE _ _ (hBZ U p q 1 (by omega))) ≫
            (eH U p q).hom =
          g ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (D : FilteredComplexPageDifferential U.obj.obj U.obj.filtration 1) :
    ∀ p q : ℤ,
          ∃ (i : U.obj.filtration.gradedPiece (p + 1) ⟶
              U.obj.filtration.complexQuotient p (p + 2) (by omega))
            (j : U.obj.filtration.complexQuotient p (p + 2) (by omega) ⟶
              U.obj.filtration.gradedPiece p)
            (hij : i ≫ j = 0) (hS : (ShortComplex.mk i j hij).ShortExact),
            U.obj.filtration.complexQuotientπ (p + 1) (p + 1 + 1) (by omega) ≫ i =
              Subobject.ofLE (U.obj.filtration.step (p + 1))
                (U.obj.filtration.step p) (U.obj.filtration.antitone_step (by omega)) ≫
                  U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ∧
            U.obj.filtration.complexQuotientπ p (p + 2) (by omega) ≫ j =
              U.obj.filtration.complexQuotientπ p (p + 1) (by omega) ∧
            D.d (p, q) (p + 1, q) ≫
                (eH U (p + 1) q).hom =
              (eH U p q).hom ≫
                hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega) := by
  intro p q
  let F := U.obj.filtration
  have hp₂ : p ≤ p + 2 := by omega
  obtain ⟨i, j, hij, hS, hi, hj⟩ := filtered_quotient_sequence F p (p + 2) (by omega)
  refine ⟨i, j, hij, hS, hi, hj, ?_⟩
  have hpq : (ComplexShape.up' (1, 1 - 1)).Rel (p, q) (p + 1, q) := by
    change (p, q) + (1, 1 - 1) = (p + 1, q)
    ext <;> simp
  obtain ⟨A, t, t', x, y, hex, ht, hx, hy⟩ :=
    filteredComplex_differential_representatives_cover U.obj.obj F 1
      (p, q) (p + 1, q) hpq
  dsimp only [Prod.fst, Prod.snd] at ht hx hy
  have hxR : (F.complexCycleRepresentatives p (p + q) 1).Factors t := by
    apply representative_factors F p (p + q) (p + 1 + q) (by omega)
    have hh := imageSubobject_factors_comp_self
      ((F.step (p + 1)).arrow.f (p + 1 + q)) t'
    rw [← ht] at hh
    exact hh
  have hyR : (F.complexCycleRepresentatives (p + 1) (p + 1 + q) 1).Factors t' := by
    apply representative_factors F (p + 1) (p + 1 + q) (p + 1 + q + 1) rfl
    have hz : t' ≫ (F.step (p + 1)).arrow.f (p + 1 + q) ≫
        U.obj.obj.d (p + 1 + q) (p + 1 + q + 1) = 0 := by
      rw [← Category.assoc, ← ht]
      simp only [Category.assoc, U.obj.obj.d_comp_d, comp_zero]
    rw [hz]
    exact Subobject.factors_zero
  obtain ⟨zx, gx, hzx, hgx, _, hxe⟩ := hH U p q
  obtain ⟨zy, gy, hzy, hgy, _, hye⟩ := hH U (p + 1) q
  let ax := Subobject.factorThru _ t hxR
  let ay := Subobject.factorThru _ t' hyR
  let cx := ax ≫ gx
  let cy := ay ≫ gy
  have hcx : cx ≫ (F.gradedPiece p).iCycles (p + q) =
      t ≫ (F.complexQuotientπ p (p + 1) (by omega)).f (p + q) := by
    dsimp [cx, ax]
    rw [Category.assoc, hgx, ← Category.assoc]
    simp [F]
  have hcy : cy ≫ (F.gradedPiece (p + 1)).iCycles (p + 1 + q) =
      t' ≫ (F.complexQuotientπ (p + 1) (p + 1 + 1) (by omega)).f (p + 1 + q) := by
    dsimp [cy, ay]
    rw [Category.assoc, hgy, ← Category.assoc]
    simp [F]
  have ex := representative_normalization F p (p + q)
    (filteredComplexPageπ U.obj.obj F 1 (p, q)) (eH U p q).hom
    zx gx hzx hgx hxe t hxR x cx hx hcx
  have ey := representative_normalization F (p + 1) (p + 1 + q)
    (filteredComplexPageπ U.obj.obj F 1 (p + 1, q)) (eH U (p + 1) q).hom
    zy gy hzy hgy hye t' hyR y cy hy hcy
  let b := t ≫ (F.complexQuotientπ p (p + 2) hp₂).f (p + q)
  have hb : b ≫ j.f (p + q) = cx ≫ (F.gradedPiece p).iCycles (p + q) := by
    rw [hcx]
    simpa only [b, HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun φ ↦ t ≫ φ.f (p + q)) hj
  let inc := Subobject.ofLE (F.step (p + 1)) (F.step p)
    (F.antitone_step (by omega))
  have hinc : inc.f (p + 1 + q) ≫ (F.step p).arrow.f (p + 1 + q) =
      (F.step (p + 1)).arrow.f (p + 1 + q) := by
    simpa only [inc, HomologicalComplex.comp_f] using congrArg
      (fun φ : (F.step (p + 1) : CochainComplex C ℤ) ⟶ U.obj.obj ↦ φ.f (p + 1 + q))
      (Subobject.ofLE_arrow (F.antitone_step (show p ≤ p + 1 by omega)))
  have hd : t ≫ (F.step p : CochainComplex C ℤ).d (p + q) (p + 1 + q) =
      t' ≫ inc.f (p + 1 + q) := by
    apply (cancel_mono ((F.step p).arrow.f (p + 1 + q))).1
    calc
      _ = t ≫ (F.step p).arrow.f (p + q) ≫ U.obj.obj.d (p + q) (p + 1 + q) := by
        simpa only [Category.assoc] using congrArg (fun f ↦ t ≫ f)
          ((F.step p).arrow.comm (p + q) (p + 1 + q)).symm
      _ = t' ≫ (F.step (p + 1)).arrow.f (p + 1 + q) := ht
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f ↦ t' ≫ f) hinc.symm
  have hc : cy ≫ (F.gradedPiece (p + 1)).iCycles (p + 1 + q) ≫ i.f (p + 1 + q) =
      b ≫ (F.complexQuotient p (p + 2) hp₂).d (p + q) (p + 1 + q) := by
    have hi' := congrArg (fun φ ↦ t' ≫ φ.f (p + 1 + q)) hi
    calc
      _ = (t' ≫ (F.complexQuotientπ (p + 1) (p + 1 + 1) (by omega)).f
          (p + 1 + q)) ≫ i.f (p + 1 + q) := by
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ i.f (p + 1 + q)) hcy
      _ = (t' ≫ inc.f (p + 1 + q)) ≫
          (F.complexQuotientπ p (p + 2) hp₂).f (p + 1 + q) := by
        simpa only [HomologicalComplex.comp_f, Category.assoc] using hi'
      _ = (t ≫ (F.step p : CochainComplex C ℤ).d (p + q) (p + 1 + q)) ≫
          (F.complexQuotientπ p (p + 2) hp₂).f (p + 1 + q) :=
        congrArg (fun f ↦ f ≫
          (F.complexQuotientπ p (p + 2) hp₂).f (p + 1 + q)) hd.symm
      _ = _ := by
        simpa only [b, Category.assoc] using congrArg (fun f ↦ t ≫ f)
          ((F.complexQuotientπ p (p + 2) hp₂).comm (p + q) (p + 1 + q)).symm
  have hδ := connecting_representative hS (p + q) (p + 1 + q)
    (by simp [ComplexShape.up]; omega) cx b cy hb hc
  have : Epi (filteredComplexPageπ U.obj.obj F 1 (p, q)) := by
    unfold filteredComplexPageπ
    infer_instance
  apply (cancel_epi (x ≫ filteredComplexPageπ U.obj.obj F 1 (p, q))).1
  have hD := D.on_representatives A (p, q) (p + 1, q) hpq t t' x y ht hx hy
  calc
    (x ≫ filteredComplexPageπ U.obj.obj F 1 (p, q)) ≫
        (D.d (p, q) (p + 1, q) ≫ (eH U (p + 1) q).hom) =
        y ≫ filteredComplexPageπ U.obj.obj F 1 (p + 1, q) ≫
          (eH U (p + 1) q).hom := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ (eH U (p + 1) q).hom) hD
    _ = cy ≫ (F.gradedPiece (p + 1)).homologyπ (p + 1 + q) := ey
    _ = cx ≫ (F.gradedPiece p).homologyπ (p + q) ≫
        hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega) := hδ.symm
    _ = (x ≫ filteredComplexPageπ U.obj.obj F 1 (p, q)) ≫
        ((eH U p q).hom ≫
          hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫
        hS.δ (p + q) (p + 1 + q) (by simp [ComplexShape.up]; omega)) ex.symm

end CategoryTheory
