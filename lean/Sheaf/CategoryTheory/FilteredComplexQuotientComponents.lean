/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.CategoryTheory.FilteredComplexPageDifferential

/-! # Maps of concrete graded cycles and their boundary quotients

Source: Stacks Project, Homology, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-quotient-components).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem image_square_le {A B A' B' : C}
    (q : A ⟶ B) (q' : A' ⟶ B') (s : A ⟶ A') (t : B ⟶ B')
    (h : q ≫ t = s ≫ q') (U : Subobject A) (U' : Subobject A')
    (hU : U ≤ (Subobject.pullback s).obj U') :
    (Subobject.«exists» q).obj U ≤
      (Subobject.pullback t).obj ((Subobject.«exists» q').obj U') := by
  apply leOfHom
  refine ((Subobject.existsPullbackAdj q).homEquiv _ _).symm ?_
  apply homOfLE
  rw [← Subobject.pullback_comp, h, Subobject.pullback_comp]
  exact hU.trans ((Subobject.pullback s).monotone
    (leOfHom ((Subobject.existsPullbackAdj q').unit.app U')))

private theorem inf_square_le {A B : C} (b : A ⟶ B)
    (P Q : Subobject A) (P' Q' : Subobject B)
    (hP : P ≤ (Subobject.pullback b).obj P')
    (hQ : Q ≤ (Subobject.pullback b).obj Q') :
    P ⊓ Q ≤ (Subobject.pullback b).obj (P' ⊓ Q') := by
  apply Subobject.le_of_factors
  apply (pullback_factors_iff _ _ _).mpr
  apply (Subobject.inf_factors _).mpr
  constructor
  · apply (pullback_factors_iff _ _ _).mp
    exact Subobject.factors_of_le _ (inf_le_left.trans hP) (P ⊓ Q).factors_self
  · apply (pullback_factors_iff _ _ _).mp
    exact Subobject.factors_of_le _ (inf_le_right.trans hQ) (P ⊓ Q).factors_self

private theorem sup_square_le {A B : C} (b : A ⟶ B)
    (P Q : Subobject A) (P' Q' : Subobject B)
    (hP : P ≤ (Subobject.pullback b).obj P')
    (hQ : Q ≤ (Subobject.pullback b).obj Q') :
    P ⊔ Q ≤ (Subobject.pullback b).obj (P' ⊔ Q') := by
  exact sup_le (hP.trans ((Subobject.pullback b).monotone le_sup_left))
    (hQ.trans ((Subobject.pullback b).monotone le_sup_right))

/-- A filtered chain map induces maps on graded pieces, graded cycles, and their
boundary quotients, with the two projection squares commuting.
Source: Stacks Project, Homology, Tag 012K, lemma-functorial.
(blueprint: lem-weil-pbc-filtered-quotient-components).

Proof. The restrictions s commute with the inclusions of successive filtration
steps: compose both candidate maps with the target step inclusion, use hs, and
cancel that monomorphism. The cokernel universal property gives t on graded
pieces and its projection square. The chain-map equation for b takes the
intersection F^p with d-inverse(F^(p+r)) into its target counterpart, and takes
F^(p+1) into F'^(p+1). Taking sums, pullbacks to F^p, and graded images therefore
gives the map g on graded cycles, with its inclusion square. The same chain-map
equation takes the image of d on F^(p-r+1) into the corresponding target image.
Intersecting with F^p, adding F^(p+1), and taking graded images gives a map on
boundaries. The inclusion square for boundaries and cycles follows by canceling
the target graded-cycle inclusion. Applying cokernel.map to this square gives m
and the quotient projection square. This construction uses only finite limits,
images, and cokernels; it works also at the zero filtration or zero complex and
requires no projective objects or finiteness hypotheses. -/
theorem filteredComplex_quotient_components
    (K K' : CochainComplex C ℤ) (F : DecreasingFiltration K) (F' : DecreasingFiltration K')
    (b : K ⟶ K')
    (s : ∀ p : ℤ, (F.step p : CochainComplex C ℤ) ⟶
      (F'.step p : CochainComplex C ℤ))
    (hs : ∀ p, s p ≫ (F'.step p).arrow = (F.step p).arrow ≫ b) :
    ∃ (t : ∀ p n : ℤ, (F.gradedPiece p).X n ⟶ (F'.gradedPiece p).X n)
      (g : ∀ (r : ℤ) (_hr : 1 ≤ r) (pq : ℤ × ℤ),
        (F.complexCycles pq.1 (pq.1 + pq.2) r : C) ⟶
          (F'.complexCycles pq.1 (pq.1 + pq.2) r : C))
      (m : ∀ (r : ℤ) (_hr : 1 ≤ r) (pq : ℤ × ℤ),
        filteredComplexPageObject K F r pq ⟶ filteredComplexPageObject K' F' r pq),
      (∀ p n, (s p).f n ≫ (F'.complexQuotientπ p (p + 1) (by omega)).f n =
        (F.complexQuotientπ p (p + 1) (by omega)).f n ≫ t p n) ∧
      (∀ r hr pq, g r hr pq ≫ (F'.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
        (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫ t pq.1 (pq.1 + pq.2)) ∧
      (∀ r hr pq, filteredComplexPageπ K F r pq ≫ m r hr pq =
        g r hr pq ≫ filteredComplexPageπ K' F' r pq) := by
  classical
  have hsi (p n : ℤ) : (s p).f n ≫ (F'.step p).arrow.f n =
      (F.step p).arrow.f n ≫ b.f n := by
    exact congrArg (fun f : (F.step p : CochainComplex C ℤ) ⟶ K' ↦ f.f n) (hs p)
  let inc (p : ℤ) := Subobject.ofLE (F.step (p + 1)) (F.step p)
    (F.antitone_step (by omega))
  let inc' (p : ℤ) := Subobject.ofLE (F'.step (p + 1)) (F'.step p)
    (F'.antitone_step (by omega))
  have hi (p : ℤ) : inc p ≫ s p = s (p + 1) ≫ inc' p := by
    apply (cancel_mono (F'.step p).arrow).1
    simp only [Category.assoc, hs, inc, inc', Subobject.ofLE_arrow,
      reassoc_of% Subobject.ofLE_arrow]
  let T (p : ℤ) : F.gradedPiece p ⟶ F'.gradedPiece p :=
    cokernel.map (inc p) (inc' p) (s (p + 1)) (s p) (hi p)
  have ht (p n : ℤ) : (s p).f n ≫
      (F'.complexQuotientπ p (p + 1) (by omega)).f n =
      (F.complexQuotientπ p (p + 1) (by omega)).f n ≫ (T p).f n := by
    have h : cokernel.π (inc p) ≫ T p = s p ≫ cokernel.π (inc' p) := by
      dsimp [T]
      exact cokernel.π_desc _ _ _
    exact (congrArg (fun f ↦ f.f n) h).symm
  have hstep (p n : ℤ) : F.complexStep p n ≤
      (Subobject.pullback (b.f n)).obj (F'.complexStep p n) := by
    unfold DecreasingFiltration.complexStep
    have hfac : ((Subobject.pullback (b.f n)).obj
        (imageSubobject ((F'.step p).arrow.f n))).Factors ((F.step p).arrow.f n) := by
      apply (pullback_factors_iff _ _ _).mpr
      rw [← hsi]
      exact imageSubobject_factors_comp_self _ _
    exact imageSubobject_le _ (Subobject.factorThru _ _ hfac)
      (Subobject.factorThru_arrow _ _ hfac)
  have hcycle (p n r : ℤ) : F.complexCycles p n r ≤
      (Subobject.pullback ((T p).f n)).obj (F'.complexCycles p n r) := by
    unfold DecreasingFiltration.complexCycles
    apply image_square_le _ _ ((s p).f n) _ (ht p n).symm
    have hpre : (Subobject.pullback (K.d n (n + 1))).obj
        (F.complexStep (p + r) (n + 1)) ≤
        (Subobject.pullback (b.f n)).obj ((Subobject.pullback (K'.d n (n + 1))).obj
          (F'.complexStep (p + r) (n + 1))) := by
      have h := (Subobject.pullback (K.d n (n + 1))).monotone (hstep (p + r) (n + 1))
      rw [← Subobject.pullback_comp, ← b.comm, Subobject.pullback_comp] at h
      exact h
    have hR := sup_square_le (b.f n) _ _ _ _
      (inf_square_le (b.f n) _ _ _ _ (hstep p n) hpre) (hstep (p + 1) n)
    have h := (Subobject.pullback ((F.step p).arrow.f n)).monotone hR
    rw [← Subobject.pullback_comp, ← hsi, Subobject.pullback_comp] at h
    exact h
  have hboundary (p n r : ℤ) : F.complexBoundaries p n r ≤
      (Subobject.pullback ((T p).f n)).obj (F'.complexBoundaries p n r) := by
    unfold DecreasingFiltration.complexBoundaries
    apply image_square_le _ _ ((s p).f n) _ (ht p n).symm
    have hR := sup_square_le (b.f n) _ _ _ _
      (inf_square_le (b.f n) _ _ _ _ (hstep p n)
        (image_square_le (K.d (n - 1) n) (K'.d (n - 1) n)
          (b.f (n - 1)) (b.f n) (b.comm (n - 1) n).symm _ _
          (hstep (p - r + 1) (n - 1)))) (hstep (p + 1) n)
    have h := (Subobject.pullback ((F.step p).arrow.f n)).monotone hR
    rw [← Subobject.pullback_comp, ← hsi, Subobject.pullback_comp] at h
    exact h
  let g (r : ℤ) (_ : 1 ≤ r) (pq : ℤ × ℤ) :=
    Subobject.factorThru (F'.complexCycles pq.1 (pq.1 + pq.2) r)
      ((F.complexCycles pq.1 (pq.1 + pq.2) r).arrow ≫ (T pq.1).f (pq.1 + pq.2))
      ((pullback_factors_iff _ _ _).mp (Subobject.factors_of_le _
        (hcycle pq.1 (pq.1 + pq.2) r) (F.complexCycles pq.1 (pq.1 + pq.2) r).factors_self))
  let k (r : ℤ) (pq : ℤ × ℤ) :=
    Subobject.factorThru (F'.complexBoundaries pq.1 (pq.1 + pq.2) r)
      ((F.complexBoundaries pq.1 (pq.1 + pq.2) r).arrow ≫ (T pq.1).f (pq.1 + pq.2))
      ((pullback_factors_iff _ _ _).mp (Subobject.factors_of_le _
        (hboundary pq.1 (pq.1 + pq.2) r)
        (F.complexBoundaries pq.1 (pq.1 + pq.2) r).factors_self))
  let β (r : ℤ) (pq : ℤ × ℤ) := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r)
  let β' (r : ℤ) (pq : ℤ × ℤ) := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K' F' pq.1 (pq.1 + pq.2) r)
  have hβ (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :
      β r pq ≫ g r hr pq = k r pq ≫ β' r pq := by
    apply (cancel_mono (F'.complexCycles pq.1 (pq.1 + pq.2) r).arrow).1
    simp only [Category.assoc, g, k, Subobject.factorThru_arrow,
      β, β', Subobject.ofLE_arrow, reassoc_of% Subobject.ofLE_arrow]
  let m (r : ℤ) (hr : 1 ≤ r) (pq : ℤ × ℤ) :=
    cokernel.map (β r pq) (β' r pq) (k r pq) (g r hr pq) (hβ r hr pq)
  refine ⟨fun p n ↦ (T p).f n, g, m, ht, ?_, ?_⟩
  · intro r hr pq
    exact Subobject.factorThru_arrow _ _ _
  · intro r hr pq
    exact cokernel.π_desc _ _ _

end CategoryTheory
