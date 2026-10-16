/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups V2, T2
-/
module

public import Sheaf.CategoryTheory.FilteredHomologyExactCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.CategoryTheory.FilteredHomologyTowerForwardRepresentatives
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.FiniteCycleFormula
import all Sheaf.CategoryTheory.FiniteCycleDerivedComparison

/-! # Representative comparisons with the canonical exact-couple tower

Source: Stacks Project, Tags 012K and 011R.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

private theorem quotient_homology_heq
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (p n p' n' : ℤ) (hp : p = p') (hn : n = n') :
    HomologicalComplex.homologyMap (F.complexQuotientπ p (p + 1) (by omega)) n ≍
      HomologicalComplex.homologyMap (F.complexQuotientπ p' (p' + 1) (by omega)) n' := by
  subst p' n'
  rfl

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
set_option linter.unusedVariables false in
/ -- The canonical derived-couple differential differentiates simultaneous filtered
representatives. The maps into the tower are fixed by their initial-homology
normalization; no quotient isomorphism is supplied or asserted here.
Source: Stacks Project, Tag 011R, derived-map restriction equations, and Tag 012K,
Lemma 12.24.2, differential on representatives.
(blueprint: lem-sp-filtered-homology-tower-differential).

Proof. The ambient differential squares to zero, and the filtration inclusion is
monic, so a' lifts uniquely to a cycle b in F^(p+s+1). Obtain the canonical
monic inclusions I of the derived D objects and the concrete iterated image
lift e of alphaIter. The forward-representative theorem identifies the page f
of x with the homology class of b followed by e. The finite-cycle formula
places initial g in the tower cycles, and the proved derived-g comparison
identifies e followed by page g with this factorization followed by the tower
projection. Naturality of homologyπ for the graded projection, together with
hy, hj and ht, identifies this factorization on b with y followed by tQ.
Compose the forward equation with g and transport the integer indices to
obtain the stated differential equation. The supplied hBZ, eH and hH are
unnecessary for this direct representative calculation. - /
theorem filteredHomology_tower_differential
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
    (s : ℕ) (p q : ℤ)
    (A : C)
    (a : A ⟶ (U.obj.filtration.step p : CochainComplex C ℤ).X (p + q))
    (a' : A ⟶ (U.obj.filtration.step (p + (s + 1)) :
      CochainComplex C ℤ).X (p + (s + 1) + (q - (s + 1) + 1)))
    (x : A ⟶ (U.obj.filtration.complexCycles p (p + q) (s + 1) : C))
    (y : A ⟶ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1) : C))
    (ha : a ≫ (U.obj.filtration.step p).arrow.f (p + q) ≫
      U.obj.obj.d (p + q) (p + (s + 1) + (q - (s + 1) + 1)) =
      a' ≫ (U.obj.filtration.step (p + (s + 1))).arrow.f
        (p + (s + 1) + (q - (s + 1) + 1)))
    (hx : x ≫ (U.obj.filtration.complexCycles p (p + q) (s + 1)).arrow =
      a ≫ (U.obj.filtration.complexQuotientπ p (p + 1) (by omega)).f (p + q))
    (hy : y ≫ (U.obj.filtration.complexCycles (p + (s + 1))
      (p + (s + 1) + (q - (s + 1) + 1)) (s + 1)).arrow =
      a' ≫ (U.obj.filtration.complexQuotientπ (p + (s + 1))
        (p + (s + 1) + 1) (by omega)).f
          (p + (s + 1) + (q - (s + 1) + 1))) :
    x ≫ tQ s p q ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * p + q) (-p) ≫
        ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).d
          (2 * p + q) (-p) ≫
        eqToHom (congrArg₂
          ((filteredHomologyExactCouple U.obj.obj U.obj.filtration).pageCouple s).E
          (show 2 * p + q + 2 + s =
            2 * (p + (s + 1)) + (q - (s + 1) + 1) by omega)
          (show -p - 1 - s = -(p + (s + 1)) by omega)) =
      y ≫ tQ s (p + (s + 1)) (q - (s + 1) + 1) ≫
        (filteredHomologyExactCouple U.obj.obj U.obj.filtration).cycleBoundaryTower.projection
          s (2 * (p + (s + 1)) + (q - (s + 1) + 1)) (-(p + (s + 1))) := by
  clear hH eH hBZ
  let F := U.obj.filtration
  let X := filteredHomologyExactCouple U.obj.obj F
  let T := X.cycleBoundaryTower
  let p' := p + (s + 1)
  let q' := q - (s + 1) + 1
  let P := 2 * p' + q'
  let Q := -p'
  let n' := p' + q'
  have hda' : a' ≫ (F.step p' : CochainComplex C ℤ).d n' (n' + 1) = 0 := by
    apply (cancel_mono ((F.step p').arrow.f (n' + 1))).mp
    simp only [Category.assoc, zero_comp]
    rw [← (F.step p').arrow.comm]
    rw [← Category.assoc a', ← ha]
    simp only [n', p', q', Category.assoc, U.obj.obj.d_comp_d, comp_zero]
  let b : A ⟶ (F.step p' : CochainComplex C ℤ).cycles n' :=
    (F.step p' : CochainComplex C ℤ).liftCycles (i := n') a' (n' + 1) (by simp) hda'
  have hb : b ≫ (F.step p' : CochainComplex C ℤ).iCycles n' = a' := by
    simp only [b, HomologicalComplex.liftCycles_i]
  obtain ⟨_, I, _, _, hI0, hIs, hImono, _, _⟩ := X.pageCouple_image_prefix
  let e := BigradedExactCouple.comparisonLift X s P Q
  have he : e ≫ I s (P - s) (Q + s) = X.alphaIter s P Q :=
    BigradedExactCouple.comparisonLift_inclusion X I hI0 hIs s P Q
  have haB : a ≫ (F.step p).arrow.f (p + q) ≫ U.obj.obj.d (p + q) n' =
      b ≫ (F.step p' : CochainComplex C ℤ).iCycles n' ≫ (F.step p').arrow.f n' := by
    rw [← Category.assoc b, hb]
    exact ha
  have hf := filteredHomology_tower_forward_representatives C U j tQ hj ht
    I hI0 hIs hImono s p q e he A a b x haB hx
  let eD : (F.step p' : CochainComplex C ℤ).homology n' ≅ X.D P Q :=
    eqToIso (by
      change (F.step p' : CochainComplex C ℤ).homology n' =
        (F.step (-Q) : CochainComplex C ℤ).homology (P + Q)
      dsimp [P, Q, n']
      rw [neg_neg]
      congr 1; omega)
  let β := b ≫ (F.step p' : CochainComplex C ℤ).homologyπ n' ≫ eD.hom
  change x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
      (X.pageCouple s).f (2 * p + q) (-p) ≫ _ =
      b ≫ (F.step p' : CochainComplex C ℤ).homologyπ n' ≫ eD.hom ≫ e at hf
  have hg : (T.Z s P Q).Factors (X.initialG P Q) := by
    rw [BigradedExactCouple.finiteCycle_formula]
    apply pullback_factors
    have hgf : X.initialG P Q ≫ X.f P Q = 0 := by
      rw [BigradedExactCouple.initialG, Category.assoc,
        ← eqToHom_naturality (fun pq : ℤ × ℤ ↦ X.f pq.1 pq.2)
          (show (P + (0 : ℕ), Q - (0 : ℕ)) = (P, Q) by ext <;> simp),
        ← Category.assoc, X.f_g_zero, zero_comp]
    rw [hgf]
    exact Subobject.factors_zero
  let c := (T.Z s P Q).factorThru (X.initialG P Q) hg
  have hG := X.finiteCycle_derived_comparison I hI0 hIs hImono s P Q hg e he
  have hgnorm : eD.hom ≫ X.initialG P Q ≫ (filteredHomologyEIso U.obj.obj F p' q').hom =
      HomologicalComplex.homologyMap (F.complexQuotientπ p' (p' + 1) (by omega)) n' := by
    apply eq_of_heq
    simp only [eD, filteredHomologyEIso, eqToIso.hom, BigradedExactCouple.initialG,
      X, filteredHomologyExactCouple, BigradedExactCouple.ofShifted_g,
      filteredHomologyG, ← Category.assoc, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact quotient_homology_heq U.obj.obj F _ _ _ _
      (by dsimp [Q]; omega) (by dsimp [P, Q, n']; omega)
  have hcycles : b ≫ HomologicalComplex.cyclesMap
      (F.complexQuotientπ p' (p' + 1) (by omega)) n' = y ≫ j s p' q' := by
    dsimp only [F, n']
    apply (cancel_mono ((U.obj.filtration.gradedPiece p').iCycles (p' + q'))).mp
    erw [Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc b, hb, Category.assoc y, hj]
    exact hy.symm
  have hcy : β ≫ c = y ≫ tQ s p' q' := by
    apply (cancel_mono (T.Z s P Q).arrow).mp
    apply (cancel_mono (filteredHomologyEIso U.obj.obj F p' q').hom).mp
    simp only [β, c, Category.assoc, Subobject.factorThru_arrow]
    erw [hgnorm, HomologicalComplex.homologyπ_naturality,
      ← Category.assoc b, hcycles]
    dsimp only [F, X, T, P, Q, n']
    erw [Category.assoc, ← ht s p' q']
  have hfg := congrArg
    (fun f ↦ f ≫ (X.pageCouple s).g (P - s) (Q + s) ≫
      eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
        (X.pageCouple s).E P Q by congr 1 <;> omega)) hf
  have hleft : x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
      (X.pageCouple s).d (2 * p + q) (-p) ≫
        eqToHom (show (X.pageCouple s).E (2 * p + q + 2 + s) (-p - 1 - s) =
          (X.pageCouple s).E P Q by congr 1 <;> dsimp [P, Q, p', q'] <;> omega) =
      x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
        (X.pageCouple s).f (2 * p + q) (-p) ≫
          eqToHom (show (X.pageCouple s).D (2 * p + q + 2) (-p - 1) =
            (X.pageCouple s).D (P - s) (Q + s) by
              congr 1 <;> dsimp [P, Q, p', q'] <;> omega) ≫
          (X.pageCouple s).g (P - s) (Q + s) ≫
          eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
            (X.pageCouple s).E P Q by congr 1 <;> omega) := by
    have hnat := eqToHom_naturality (fun pq : ℤ × ℤ ↦ (X.pageCouple s).g pq.1 pq.2)
      (show (2 * p + q + 2, -p - 1) = (P - s, Q + s) by
        ext <;> dsimp [P, Q, p', q'] <;> omega)
    have hnat' := congrArg (fun f ↦ f ≫
      eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
        (X.pageCouple s).E P Q by congr 1 <;> omega)) hnat
    simp only [Category.assoc, eqToHom_trans] at hnat'
    simpa only [BigradedExactCouple.d, Category.assoc] using congrArg
      (fun f ↦ x ≫ tQ s p q ≫ T.projection s (2 * p + q) (-p) ≫
        (X.pageCouple s).f (2 * p + q) (-p) ≫ f) hnat'
  calc
    _ = _ := hleft
    _ = β ≫ e ≫ (X.pageCouple s).g (P - s) (Q + s) ≫
        eqToHom (show (X.pageCouple s).E (P - s + s) (Q + s - s) =
          (X.pageCouple s).E P Q by congr 1 <;> omega) := by
      simpa only [β, Category.assoc] using hfg
    _ = β ≫ c ≫ T.projection s P Q := by
      simpa only [c, Category.assoc] using congrArg (fun f ↦ β ≫ f) hG
    _ = _ := by
      rw [← Category.assoc, hcy]
      dsimp only [F, X, T, P, Q, p', q']
      simp only [Category.assoc]
-/

end CategoryTheory
