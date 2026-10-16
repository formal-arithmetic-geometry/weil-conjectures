/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence

/-! # The forward map on filtered representatives

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem inclusion_homology_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (a b a' b' n n' : ℤ) (h : b ≤ a) (h' : b' ≤ a')
    (ha : a = a') (hb : b = b') (hn : n = n') :
    HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step a) (F.step b) (F.antitone_step h)) n ≍
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step a') (F.step b') (F.antitone_step h')) n' := by
  subst a' b' n'
  rfl

private theorem filtered_alphaIter
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (s : ℕ) (P Q : ℤ) :
    (filteredHomologyExactCouple K F).alphaIter s P Q ≍
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step (-Q)) (F.step (-(Q + (s : ℤ))))
          (F.antitone_step (by omega))) (P + Q) := by
  induction s generalizing P Q with
  | zero =>
    simp only [BigradedExactCouple.alphaIter]
    apply (eqToHom_heq_id_dom _ _ _).trans
    have hh : HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step (-Q)) (F.step (-Q)) le_rfl) (P + Q) = 𝟙 _ := by
      simp
    apply (heq_of_eq hh).symm.trans
    exact inclusion_homology_heq K F _ _ _ _ _ _ le_rfl (by omega) rfl (by omega) rfl
  | succ s ih =>
    let l := Subobject.ofLE (F.step (-Q)) (F.step (-(Q + 1)))
      (F.antitone_step (by omega))
    let m := Subobject.ofLE (F.step (-(Q + 1))) (F.step (-(Q + 1 + (s : ℤ))))
      (F.antitone_step (by omega))
    have h : (filteredHomologyExactCouple K F).alphaIter (s + 1) P Q ≍
        HomologicalComplex.homologyMap l (P + Q) ≫
          HomologicalComplex.homologyMap m (P + Q) := by
      simp only [BigradedExactCouple.alphaIter, filteredHomologyExactCouple,
        BigradedExactCouple.ofShifted_alpha]
      simp only [filteredHomologyAlpha, Category.assoc]
      apply heq_comp rfl rfl (by
        change (F.step (-(Q + (s + 1 : ℕ))) : CochainComplex C ℤ).homology
          (P - (s + 1 : ℕ) + (Q + (s + 1 : ℕ))) = _
        apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n) <;> omega)
        HEq.rfl
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      apply (ih (P - 1) (Q + 1)).trans
      exact inclusion_homology_heq K F _ _ _ _ _ _ (by omega) (by omega)
        rfl rfl (by omega)
    apply h.trans
    rw [← HomologicalComplex.homologyMap_comp]
    dsimp only [l, m]
    rw [Subobject.ofLE_comp_ofLE]
    exact inclusion_homology_heq K F _ _ _ _ _ _ (by omega) (by omega)
      rfl (by omega) rfl

private theorem connecting_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n p' n' : ℤ) (hp : p = p') (hn : n = n') :
    (filteredStep_shortExact K F p).δ n (n + 1) rfl ≍
      (filteredStep_shortExact K F p').δ n' (n' + 1) rfl := by
  subst p' n'
  rfl

private theorem filtered_initial_f
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (p q : ℤ) :
    (filteredHomologyEIso K F p q).inv ≫
        (filteredHomologyExactCouple K F).f (2 * p + q) (-p) ≍
      (filteredStep_shortExact K F p).δ (p + q) (p + q + 1) rfl := by
  simp only [filteredHomologyEIso, eqToIso, filteredHomologyExactCouple,
    BigradedExactCouple.ofShifted_f, filteredHomologyF,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact connecting_heq K F _ _ _ _ (by omega) (by omega)

private theorem connecting_representative
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n r : ℤ) (hr : 1 ≤ r) {A : C}
    (a : A ⟶ (F.step p : CochainComplex C ℤ).X n)
    (a' : A ⟶ (F.step (p + r) : CochainComplex C ℤ).X (n + 1))
    (g : A ⟶ (F.gradedPiece p).cycles n)
    (ha : a ≫ (F.step p).arrow.f n ≫ K.d n (n + 1) =
      a' ≫ (F.step (p + r)).arrow.f (n + 1))
    (hg : g ≫ (F.gradedPiece p).iCycles n =
      a ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n) :
    ∃ z : A ⟶ (F.step (p + r) : CochainComplex C ℤ).cycles (n + 1),
      z ≫ (F.step (p + r) : CochainComplex C ℤ).iCycles (n + 1) = a' ∧
      g ≫ (F.gradedPiece p).homologyπ n ≫
          (filteredStep_shortExact K F p).δ n (n + 1) rfl =
        z ≫ (F.step (p + r) : CochainComplex C ℤ).homologyπ (n + 1) ≫
          HomologicalComplex.homologyMap
            (Subobject.ofLE (F.step (p + r)) (F.step (p + 1))
              (F.antitone_step (by omega))) (n + 1) := by
  let l := Subobject.ofLE (F.step (p + r)) (F.step (p + 1))
    (F.antitone_step (by omega))
  have hz : a' ≫ (F.step (p + r) : CochainComplex C ℤ).d (n + 1) (n + 2) = 0 := by
    apply (cancel_mono ((F.step (p + r)).arrow.f (n + 2))).mp
    rw [Category.assoc, ← (F.step (p + r)).arrow.comm, ← Category.assoc,
      ← ha, Category.assoc, Category.assoc, K.d_comp_d, comp_zero, comp_zero,
      zero_comp]
  let z := (F.step (p + r) : CochainComplex C ℤ).liftCycles a' (n + 2) (by simp; omega) hz
  have hzi : z ≫ (F.step (p + r) : CochainComplex C ℤ).iCycles (n + 1) = a' :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  have hb : (a' ≫ l.f (n + 1)) ≫
      (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))).f
        (n + 1) = a ≫ (F.step p : CochainComplex C ℤ).d n (n + 1) := by
    apply (cancel_mono ((F.step p).arrow.f (n + 1))).mp
    simp only [Category.assoc, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
    simp only [l, Subobject.ofLE_arrow]
    rw [← (F.step p).arrow.comm]
    exact ha.symm
  have hδ := (filteredStep_shortExact K F p).δ_eq n (n + 1) rfl
    (g ≫ (F.gradedPiece p).iCycles n)
    (by
      change (g ≫ (F.gradedPiece p).iCycles n) ≫ (F.gradedPiece p).d n (n + 1) = 0
      simp only [Category.assoc, HomologicalComplex.iCycles_d, comp_zero])
    a hg.symm (a' ≫ l.f (n + 1)) hb (n + 2) (by simp; omega)
  dsimp only at hδ
  have hg' : (F.gradedPiece p).liftCycles
      (g ≫ (F.gradedPiece p).iCycles n) (n + 1) (by simp) (by simp) = g := by
    apply (cancel_mono ((F.gradedPiece p).iCycles n)).mp
    simp
  have hz' : (F.step (p + 1) : CochainComplex C ℤ).liftCycles
      (a' ≫ l.f (n + 1)) (n + 2) (by simp; omega) (by
        rw [Category.assoc, l.comm, ← Category.assoc, hz, zero_comp]) =
        z ≫ HomologicalComplex.cyclesMap l (n + 1) := by
    apply (cancel_mono ((F.step (p + 1) : CochainComplex C ℤ).iCycles (n + 1))).mp
    rw [HomologicalComplex.liftCycles_i, Category.assoc,
      HomologicalComplex.cyclesMap_i, ← Category.assoc, hzi]
  refine ⟨z, hzi, ?_⟩
  erw [hg', hz'] at hδ
  simpa only [l, DecreasingFiltration.complexQuotient,
    DecreasingFiltration.gradedPiece, DecreasingFiltration.gr, Category.assoc,
    HomologicalComplex.homologyπ_naturality] using hδ

private theorem connecting_from_cycle
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n r m : ℤ) (hr : 1 ≤ r) (hm : n + 1 = m) {A : C}
    (a : A ⟶ (F.step p : CochainComplex C ℤ).X n)
    (b : A ⟶ (F.step (p + r) : CochainComplex C ℤ).cycles m)
    (g : A ⟶ (F.gradedPiece p).cycles n)
    (ha : a ≫ (F.step p).arrow.f n ≫ K.d n m =
      b ≫ (F.step (p + r) : CochainComplex C ℤ).iCycles m ≫
        (F.step (p + r)).arrow.f m)
    (hg : g ≫ (F.gradedPiece p).iCycles n =
      a ≫ (F.complexQuotientπ p (p + 1) (by omega)).f n) :
    g ≫ (F.gradedPiece p).homologyπ n ≫
        (filteredStep_shortExact K F p).δ n m (by subst m; rfl) =
      b ≫ (F.step (p + r) : CochainComplex C ℤ).homologyπ m ≫
        HomologicalComplex.homologyMap
          (Subobject.ofLE (F.step (p + r)) (F.step (p + 1))
            (F.antitone_step (by omega))) m := by
  subst m
  obtain ⟨z, hz, hδ⟩ := connecting_representative K F p n r hr a
    (b ≫ (F.step (p + r) : CochainComplex C ℤ).iCycles (n + 1)) g
    (by simpa only [Category.assoc] using ha) hg
  have hzb : z = b := (cancel_mono
    ((F.step (p + r) : CochainComplex C ℤ).iCycles (n + 1))).mp hz
  simpa only [hzb] using hδ

private theorem connecting_index_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n m : ℤ) (hm : n + 1 = m) :
    (filteredStep_shortExact K F p).δ n (n + 1) rfl ≍
      (filteredStep_shortExact K F p).δ n m (by subst m; rfl) := by
  subst m
  rfl

private theorem tower_forward_inclusion
    {C : Type u} [Category.{v} C] [Abelian C] (X : BigradedExactCouple C 0)
    (I : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (hI0 : ∀ p q : ℤ, I 0 p q = 𝟙 _)
    (hIs : ∀ (r : ℕ) (p q : ℤ), I (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ I r p q)
    (r : ℕ) (p q : ℤ) :
    X.cycleBoundaryTower.projection r p q ≫ (X.pageCouple r).f p q ≫
        I r (p + 2) (q - 1) =
      (X.cycleBoundaryTower.Z r p q).arrow ≫ X.f p q := by
  let T := X.cycleBoundaryTower
  change T.projection r p q ≫ (X.pageCouple r).f p q ≫ I r (p + 2) (q - 1) =
    (T.Z r p q).arrow ≫ X.f p q
  induction r with
  | zero =>
    simp only [hI0, T.projection_zero, BigradedExactCouple.pageCouple, Category.comp_id]
  | succ r ih =>
    let Y := X.pageCouple r
    let M := Classical.choice Y.derivedMaps_exists
    have hf : Y.derivedEProjection p q ≫ (X.pageCouple (r + 1)).f p q ≫
        Y.derivedDInclusion (p + 2) (q - 1) = kernel.ι (Y.d p q) ≫ Y.f p q :=
      by simpa only [BigradedExactCouple.pageCouple, BigradedExactCouple.derived_f]
        using M.f_comm p q
    rw [T.projection_succ, hIs]
    calc
      (T.cycleLift r p q ≫ Y.derivedEProjection p q) ≫
          (X.pageCouple (r + 1)).f p q ≫
            Y.derivedDInclusion (p + 2) (q - 1) ≫ I r (p + 2) (q - 1) =
          T.cycleLift r p q ≫ (kernel.ι (Y.d p q) ≫ Y.f p q) ≫
            I r (p + 2) (q - 1) := by
        simpa only [Category.assoc] using congrArg
          (fun z ↦ T.cycleLift r p q ≫ z ≫ I r (p + 2) (q - 1)) hf
      _ = (T.Z (r + 1) p q).arrow ≫ X.f p q := by
        calc
          T.cycleLift r p q ≫ (kernel.ι (Y.d p q) ≫ Y.f p q) ≫
              I r (p + 2) (q - 1) =
              (T.cycleLift r p q ≫ kernel.ι (Y.d p q)) ≫
                Y.f p q ≫ I r (p + 2) (q - 1) := by simp only [Category.assoc]
          _ = Subobject.ofLE _ _ (T.Z_decreasing r p q) ≫
              (T.projection r p q ≫ (X.pageCouple r).f p q ≫
                I r (p + 2) (q - 1)) := by
            rw [T.cycleLift_comm]
            simp only [Category.assoc]
            rfl
          _ = (T.Z (r + 1) p q).arrow ≫ X.f p q := by
            rw [ih, Subobject.ofLE_arrow_assoc]

/-- The forward map of the derived couple is the lifted connecting class, before applying g.
Source: Stacks Project, Tag 012K, representative differential formula preceding Lemma 12.24.2;
Tag 011R, the restriction equation for the derived forward map.
(blueprint: lem-sp-filtered-homology-tower-forward-representatives).

Proof. Let X be the initial couple and T its canonical cycle tower. Induct on n to show
T.projection n followed by page f and I n equals T.Z(n).arrow followed by original f.
At zero use projection_zero and hI0. At the successor substitute projection_succ and hIs,
then use the derived f restriction equation, cycleLift_comm and the induction hypothesis.
The normalization ht therefore identifies the left side after I with the connecting class
of a in H(F^(p+1)). The short-exact-sequence connecting-map representative formula sends
this class to the class of b included from F^(p+s+1) into F^(p+1): the supplied ha is exactly
the differential equation needed in that formula, and hx and hj give its graded cycle.
Expanding filteredHomologyAlpha and inducting on s shows that alphaIter s is homology
of that same filtration inclusion. The cycle b determines the source homology class
without any epimorphic refinement. Thus he gives the identical composite for the right
side after I. Cancel the monomorphism hImono. The index transports express the equalities
P=2*(p+s+1)+(q-s) and Q=-(p+s+1); they preserve the total degree p+q+1.
This establishes only the forward-map identity; the induced g comparison is separate. -/
theorem filteredHomology_tower_forward_representatives
    (C : Type u) [Category.{v} C] [Abelian C]
    (U : ObjectProperty.FullSubcategory
          (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite))
    (j : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        (U.obj.filtration.gradedPiece p).cycles (p + q))
    (tQ : ∀ (s : ℕ) (p q : ℤ),
      (U.obj.filtration.complexCycles p (p + q) (s + 1) : C) ⟶
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
          s (2 * p + q) (-p) : C))
    (hj : ∀ (s : ℕ) (p q : ℤ),
      j s p q ≫ (U.obj.filtration.gradedPiece p).iCycles (p + q) =
        (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow)
    (ht : ∀ (s : ℕ) (p q : ℤ),
      tQ s p q ≫
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.Z
            s (2 * p + q) (-p)).arrow ≫
          (filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom =
        j s p q ≫ (U.obj.filtration.gradedPiece p).homologyπ (p + q))
    (I : ∀ (n : ℕ) (P Q : ℤ),
      ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple n).D P Q ⟶
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).D P Q)
    (hI0 : ∀ P Q : ℤ, I 0 P Q = 𝟙 _)
    (hIs : ∀ (n : ℕ) (P Q : ℤ), I (n + 1) P Q =
      ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple n).derivedDInclusion
        P Q ≫ I n P Q)
    (hImono : ∀ (n : ℕ) (P Q : ℤ), Mono (I n P Q))
    (s : ℕ) (p q : ℤ)
    (e : (filteredHomologyExactCouple U.obj.obj U.obj.filtration).D
        (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1))) ⟶
      ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).D
        (2 * (p + (s + 1)) + (q - (s + 1) + 1) - s) (-(p + (s + 1)) + s))
    (he : e ≫ I s (2 * (p + (s + 1)) + (q - (s + 1) + 1) - s)
        (-(p + (s + 1)) + s) =
      (filteredHomologyExactCouple U.obj.obj U.obj.filtration).alphaIter s
        (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1))))
    (A : C)
    (a : A ⟶ (U.obj.filtration.step p : CochainComplex C ℤ).X (p + q))
    (b : A ⟶ (U.obj.filtration.step (p + (s + 1)) : CochainComplex C ℤ).cycles
      (p + (s + 1) + (q - (s + 1) + 1)))
    (x : A ⟶ (U.obj.filtration.complexCycles p (p + q) (s + 1) : C))
    (ha : a ≫ (U.obj.filtration.step p).arrow.f (p + q) ≫
        U.obj.obj.d (p + q) (p + (s + 1) + (q - (s + 1) + 1)) =
      b ≫ (U.obj.filtration.step (p + (s + 1)) : CochainComplex C ℤ).iCycles
        (p + (s + 1) + (q - (s + 1) + 1)) ≫
          (U.obj.filtration.step (p + (s + 1))).arrow.f
            (p + (s + 1) + (q - (s + 1) + 1)))
    (hx : x ≫ (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow =
      a ≫ (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q)) :
    x ≫ tQ s p q ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * p + q) (-p) ≫
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).f
          (2 * p + q) (-p) ≫
        eqToHom (show
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).D
              (2 * p + q + 2) (-p - 1) =
            ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).D
              (2 * (p + (s + 1)) + (q - (s + 1) + 1) - s)
              (-(p + (s + 1)) + s) by congr 1 <;> omega) =
      b ≫ (U.obj.filtration.step (p + (s + 1)) : CochainComplex C ℤ).homologyπ
          (p + (s + 1) + (q - (s + 1) + 1)) ≫
        eqToHom (by
          change (U.obj.filtration.step (p + (s + 1)) : CochainComplex C ℤ).homology
              (p + (s + 1) + (q - (s + 1) + 1)) =
            (U.obj.filtration.step (-(-(p + (s + 1)))) : CochainComplex C ℤ).homology
              (2 * (p + (s + 1)) + (q - (s + 1) + 1) + -(p + (s + 1)))
          rw [neg_neg]
          congr 1; omega) ≫ e := by
  let F := U.obj.filtration
  let X := filteredHomologyExactCouple U.obj.obj F
  let T := X.cycleBoundaryTower
  let p' := p + (s + 1)
  let q' := q - (s + 1) + 1
  let P := 2 * p' + q'
  let Q := -p'
  let n' := p' + q'
  have hn : p + q + 1 = n' := by dsimp [n', p', q']; omega
  let eD : (F.step p' : CochainComplex C ℤ).homology n' ≅ X.D P Q :=
    eqToIso (by
      change (F.step p' : CochainComplex C ℤ).homology n' =
        (F.step (-Q) : CochainComplex C ℤ).homology (P + Q)
      dsimp [P, Q, n']
      rw [neg_neg]
      congr 1; omega)
  let eD₁ : X.D (2 * p + q + 2) (-p - 1) ≅
      (F.step (p + 1) : CochainComplex C ℤ).homology n' :=
    eqToIso (by
      change (F.step (-(-p - 1)) : CochainComplex C ℤ).homology
        (2 * p + q + 2 + (-p - 1)) = _
      apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n)
      · omega
      · omega)
  let eD₂ : X.D (P - s) (Q + s) ≅
      (F.step (p + 1) : CochainComplex C ℤ).homology n' :=
    eqToIso (by
      change (F.step (-(Q + s)) : CochainComplex C ℤ).homology
        (P - s + (Q + s)) = _
      apply congrArg₂ (fun a n ↦ (F.step a : CochainComplex C ℤ).homology n) <;>
        dsimp [P, Q, n', p', q'] <;> omega)
  have hcomm := tower_forward_inclusion X I hI0 hIs
  have ht' : tQ s p q ≫ (T.Z s (2 * p + q) (-p)).arrow =
      j s p q ≫ (F.gradedPiece p).homologyπ (p + q) ≫
        (filteredHomologyEIso U.obj.obj F p q).inv := by
    apply (cancel_mono (filteredHomologyEIso U.obj.obj F p q).hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using ht s p q
  have hf₀ : (filteredHomologyEIso U.obj.obj F p q).inv ≫
      X.f (2 * p + q) (-p) ≫ eD₁.hom =
        (filteredStep_shortExact U.obj.obj F p).δ (p + q) n'
          (by simp [ComplexShape.up]; omega) := by
    apply eq_of_heq
    simp only [eD₁, eqToIso.hom, ← Category.assoc, comp_eqToHom_heq_iff]
    exact (filtered_initial_f U.obj.obj F p q).trans
      (connecting_index_heq U.obj.obj F p (p + q) n' hn)
  have hα : eD.hom ≫ X.alphaIter s P Q ≫ eD₂.hom =
      HomologicalComplex.homologyMap
        (Subobject.ofLE (F.step p') (F.step (p + 1)) (F.antitone_step (by
          dsimp [p']; omega))) n' := by
    apply eq_of_heq
    simp only [eD, eD₂, eqToIso.hom, ← Category.assoc,
      comp_eqToHom_heq_iff, eqToHom_comp_heq_iff]
    apply (filtered_alphaIter U.obj.obj F s P Q).trans
    exact inclusion_homology_heq U.obj.obj F _ _ _ _ _ _ (by omega)
      (by dsimp [p']; omega) (by dsimp [Q]; omega)
      (by dsimp [Q, p']; omega) (by dsimp [P, Q, n']; omega)
  have hδ := connecting_from_cycle U.obj.obj F p (p + q) (s + 1) n'
    (by omega) hn a b (x ≫ j s p q) ha (by
      rw [Category.assoc, hj]
      exact hx)
  have hIt : eqToHom (show (X.pageCouple s).D (2 * p + q + 2) (-p - 1) =
          (X.pageCouple s).D (P - s) (Q + s) by
        congr 1 <;> dsimp [P, Q, p', q'] <;> omega) ≫
      I s (P - s) (Q + s) ≫ eD₂.hom = I s (2 * p + q + 2) (-p - 1) ≫ eD₁.hom := by
    have hnat := eqToHom_naturality (fun pq : ℤ × ℤ ↦ I s pq.1 pq.2)
      (show (2 * p + q + 2, -p - 1) = (P - s, Q + s) by
        ext <;> dsimp [P, Q, p', q'] <;> omega)
    rw [← reassoc_of% hnat]
    simp only [eD₁, eD₂, eqToIso.hom, eqToHom_trans]
  change x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
      (X.pageCouple s).f (2 * p + q) (-p) ≫ _ =
    b ≫ (F.step p' : CochainComplex C ℤ).homologyπ n' ≫ eD.hom ≫ e
  have := hImono s (P - s) (Q + s)
  apply (cancel_mono (I s (P - s) (Q + s))).mp
  apply (cancel_mono eD₂.hom).mp
  simp only [Category.assoc]
  rw [reassoc_of% he, hIt, reassoc_of% (hcomm s (2 * p + q) (-p)), reassoc_of% ht', hf₀, hα]
  simpa only [Category.assoc] using hδ

end CategoryTheory
