/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
import WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality

/-! # Compatibility of the exact-couple differential

Source: Stacks Project, Etale Cohomology, Tag 0DDE, proof; Homology, Tags 011Q–011S;
blueprint sec-proper-base-change/sk-thm-properbasechange.
(blueprint: lem-weil-pbc-exact-couple-differential)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale
open CategoryTheory.TruncationExchange

/-- The exchanged truncation couples are exact, their exchange maps commute with the
connecting maps and every page differential, and their E₂ map is degree-p exchange.

Proof:
1. Apply exact inverse image to the truncation couple of K for the first couple.
   For the second, exact inverse image commutes with canonical truncation and cohomology,
   so it is the truncation couple of g' inverse image of K. Both are exact by
   lem-sp-truncation-couple-exact and lem-weil-pbc-exact-functor-bounded-below.
2. Apply lem-weil-pbc-derived-exchange-triangulated to each truncation triangle.
   Naturality gives the inclusion and projection squares; compatibility with the
   composite shift isomorphisms gives the connecting-arrow square.
3. Apply H^{p+q} to these three squares. The cohomology shift identification converts
   the third into the displayed square at (p+2,q-1). Thus tD and tE form a couple morphism
   in the convention of def-sp-exact-couple.
4. Use lem-sp-couple-morphism: differential commutation preserves kernels and boundaries,
   so tE induces the quotient map on the derived E term. Repeat on derived couples;
   this gives the maps on all pages, commuting with each differential. Page n here is
   the actual page n+2. The kernel/quotient squares specify the induced successor maps.
5. At E₂ the map is H^{p+q}(Ex on H^q(K)[-q]). Apply shift compatibility for -q and
   H^{p+q}(N[-q]) = H^p(N). Through pageIso, truncationSourceIso and truncationTargetIso,
   it is H^p(Ex on H^q(K)), as asserted; exact inverse image identifies the source with
   g inverse image of R^p f_* H^q(K).
Source: Stacks Project, Tag 0DDE, proof; Tags 011Q, 011R and 011S.
(blueprint: lem-weil-pbc-exact-couple-differential).
-/
theorem exact_couple_differential
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (a : ℤ)
    (_hT : ∀ q : ℤ, ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K).IsTorsion)
    (_hbelow : ∀ q : ℤ, q < a →
      IsZero ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K)) :
    ∃ P Q : BigradedExactCouple (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) 0,
    ∃ hPE : P.E = E (truncationPhi f g) K,
    ∃ hQE : Q.E = E (truncationPsi g' f') K,
      P.D = D (truncationPhi f g) K ∧ Q.D = D (truncationPsi g' f') K ∧
      HEq P.alpha (alpha (truncationPhi f g) K) ∧
      HEq Q.alpha (alpha (truncationPsi g' f') K) ∧
      HEq P.f (CategoryTheory.TruncationExchange.f (truncationPhi f g) K) ∧
      HEq Q.f (CategoryTheory.TruncationExchange.f (truncationPsi g' f') K) ∧
      HEq P.g (CategoryTheory.TruncationExchange.g (truncationPhi f g) K) ∧
      HEq Q.g (CategoryTheory.TruncationExchange.g (truncationPsi g' f') K) ∧
    (∀ p q : ℤ,
      alpha (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p - 1) (q + 1) =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          alpha (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q =
        tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.g (truncationPsi g' f') K p q) ∧
    (∀ p q : ℤ,
      CategoryTheory.TruncationExchange.f (truncationPhi f g) K p q ≫
          tD (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
            K (p + 2) (q - 1) =
        tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          CategoryTheory.TruncationExchange.f (truncationPsi g' f') K p q) ∧
    (∃ t : ∀ (n : ℕ) (p q : ℤ), (P.pageCouple n).E p q ⟶ (Q.pageCouple n).E p q,
      (∀ p q : ℤ, t 0 p q =
        eqToHom (congrFun (congrFun hPE p) q) ≫
          tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          eqToHom (congrFun (congrFun hQE p) q).symm) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (P.pageCouple n).d p q ≫ t n (p + 2 + n) (q - 1 - n) =
          t n p q ≫ (Q.pageCouple n).d p q) ∧
      (∀ (n : ℕ) (p q : ℤ),
        ∃ k : kernel ((P.pageCouple n).d p q) ⟶ kernel ((Q.pageCouple n).d p q),
          k ≫ kernel.ι ((Q.pageCouple n).d p q) =
            kernel.ι ((P.pageCouple n).d p q) ≫ t n p q ∧
          (P.pageCouple n).derivedEProjection p q ≫ t (n + 1) p q =
            k ≫ (Q.pageCouple n).derivedEProjection p q)) ∧
    (∀ p q : ℤ,
      tE (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq) K p q ≫
          (pageIso (truncationPsi g' f') K p q ≪≫
            truncationTargetIso g' f'
              ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom =
        (pageIso (truncationPhi f g) K p q ≪≫
          truncationSourceIso f g
            ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom ≫
        (truncationSourceIso f g
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).inv ≫
        (_root_.DerivedCategory.Plus.homologyFunctor
          (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) p).map
            ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app (sheaf K q)) ≫
        (truncationTargetIso g' f'
          ((_root_.DerivedCategory.Plus.homologyFunctor _ q).obj K) p).hom) := by
  obtain ⟨⟨P, Q, hPD, hQD, hPE, hQE, hPa, hQa, hPf, hQf, hPg, hQg⟩,
    hα, hg, hf, hpage⟩ := truncation_exchange_couple_morphism sq K
  let τ := derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq
  let d (p q : ℤ) : P.D p q ⟶ Q.D p q :=
    eqToHom (congrFun (congrFun hPD p) q) ≫ tD τ K p q ≫
      eqToHom (congrFun (congrFun hQD p) q).symm
  let e (p q : ℤ) : P.E p q ⟶ Q.E p q :=
    eqToHom (congrFun (congrFun hPE p) q) ≫ tE τ K p q ≫
      eqToHom (congrFun (congrFun hQE p) q).symm
  let T : BigradedExactCouple.CoupleMorphism P Q :=
    { tD := d
      tE := e
      alpha_comm := by
        intro p q
        have hQa' (p q : ℤ) : Q.alpha p q =
            eqToHom (congrFun (congrFun hQD p) q) ≫
              alpha (truncationPsi g' f') K p q ≫
              eqToHom (congrFun (congrFun hQD (p - 1)) (q + 1)).symm := by
          apply (conj_eqToHom_iff_heq _ _
            (congrFun (congrFun hQD p) q)
            (congrFun (congrFun hQD (p - 1)) (q + 1))).2
          refine dcongr_heq (HEq.refl q) ?_ (fun _ _ ↦ ?_)
          · intro q₁ q₂ h
            cases h
            simp only [hQD]
          · refine dcongr_heq (HEq.refl p) ?_ (fun _ _ ↦ hQa)
            intro p₁ p₂ h
            cases h
            exact congrArg (fun d : ℤ → ℤ → _ ↦
              ∀ q : ℤ, d p₁ q ⟶ d (p₁ - 1) (q + 1)) hQD
        have hPa' (p q : ℤ) : P.alpha p q =
            eqToHom (congrFun (congrFun hPD p) q) ≫
              alpha (truncationPhi f g) K p q ≫
              eqToHom (congrFun (congrFun hPD (p - 1)) (q + 1)).symm := by
          apply (conj_eqToHom_iff_heq _ _
            (congrFun (congrFun hPD p) q)
            (congrFun (congrFun hPD (p - 1)) (q + 1))).2
          refine dcongr_heq (HEq.refl q) ?_ (fun _ _ ↦ ?_)
          · intro q₁ q₂ h
            cases h
            simp only [hPD]
          · refine dcongr_heq (HEq.refl p) ?_ (fun _ _ ↦ hPa)
            intro p₁ p₂ h
            cases h
            exact congrArg (fun d : ℤ → ℤ → _ ↦
              ∀ q : ℤ, d p₁ q ⟶ d (p₁ - 1) (q + 1)) hPD
        rw [hQa', hPa']
        simp only [d, Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        rw [← Category.assoc (tD τ K p q), ← hα]
        simp only [Category.assoc]
        rfl
      f_comm := by
        intro p q
        have hQf' (p q : ℤ) : Q.f p q =
            eqToHom (congrFun (congrFun hQE p) q) ≫
              CategoryTheory.TruncationExchange.f (truncationPsi g' f') K p q ≫
              eqToHom (congrFun (congrFun hQD (p + 2)) (q - 1)).symm := by
          apply (conj_eqToHom_iff_heq _ _
            (congrFun (congrFun hQE p) q)
            (congrFun (congrFun hQD (p + 2)) (q - 1))).2
          refine dcongr_heq (HEq.refl q) ?_ (fun _ _ ↦ ?_)
          · intro q₁ q₂ h
            cases h
            simp only [hQE, hQD]
          · refine dcongr_heq (HEq.refl p) ?_ (fun _ _ ↦ hQf)
            intro p₁ p₂ h
            cases h
            exact
              congrArg₂ (fun d e : ℤ → ℤ → _ ↦
                ∀ q : ℤ, d p₁ q ⟶ e (p₁ + 2)
                  (q - 1)) hQE hQD
        have hPf' (p q : ℤ) : P.f p q =
            eqToHom (congrFun (congrFun hPE p) q) ≫
              CategoryTheory.TruncationExchange.f (truncationPhi f g) K p q ≫
              eqToHom (congrFun (congrFun hPD (p + 2)) (q - 1)).symm := by
          apply (conj_eqToHom_iff_heq _ _
            (congrFun (congrFun hPE p) q)
            (congrFun (congrFun hPD (p + 2)) (q - 1))).2
          refine dcongr_heq (HEq.refl q) ?_ (fun _ _ ↦ ?_)
          · intro q₁ q₂ h
            cases h
            simp only [hPE, hPD]
          · refine dcongr_heq (HEq.refl p) ?_ (fun _ _ ↦ hPf)
            intro p₁ p₂ h
            cases h
            exact
              congrArg₂ (fun d e : ℤ → ℤ → _ ↦
                ∀ q : ℤ, d p₁ q ⟶ e (p₁ + 2)
                  (q - 1)) hPE hPD
        rw [hQf', hPf']
        simp only [d, e, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        rw [← Category.assoc (tE τ K p q), ← hf]
        simp only [Category.assoc]
        rfl
      g_comm := by
        intro p q
        apply (cancel_mono (eqToHom (show Q.E (p + (0 : ℕ)) (q - (0 : ℕ)) =
          Q.E p q by congr 1 <;> omega))).1
        simp only [Category.assoc]
        rw [eqToHom_naturality (fun pq : ℤ × ℤ ↦ e pq.1 pq.2)
          (show (p + (0 : ℕ), q - (0 : ℕ)) = (p, q) by ext <;> omega)]
        change d p q ≫ Q.initialG p q = P.initialG p q ≫ e p q
        have hQg' (p q : ℤ) : Q.initialG p q =
            eqToHom (congrFun (congrFun hQD p) q) ≫
              CategoryTheory.TruncationExchange.g (truncationPsi g' f') K p q ≫
              eqToHom (congrFun (congrFun hQE p) q).symm := by
          apply (conj_eqToHom_iff_heq _ _
            (congrFun (congrFun hQD p) q)
            (congrFun (congrFun hQE (p)) (q))).2
          dsimp only [BigradedExactCouple.initialG]
          rw [comp_eqToHom_heq_iff]
          refine dcongr_heq (HEq.refl q) ?_ (fun _ _ ↦ ?_)
          · intro q₁ q₂ h
            cases h
            simp only [hQD, hQE, Nat.cast_zero, add_zero, sub_zero]
          · refine dcongr_heq (HEq.refl p) ?_ (fun _ _ ↦ hQg)
            intro p₁ p₂ h
            cases h
            apply congrArg (fun t : ℤ → Type _ ↦ ∀ q : ℤ, t q)
            funext q
            simp only [hQD, hQE, Nat.cast_zero, add_zero, sub_zero]
        have hPg' (p q : ℤ) : P.initialG p q =
            eqToHom (congrFun (congrFun hPD p) q) ≫
              CategoryTheory.TruncationExchange.g (truncationPhi f g) K p q ≫
              eqToHom (congrFun (congrFun hPE p) q).symm := by
          apply (conj_eqToHom_iff_heq _ _
            (congrFun (congrFun hPD p) q)
            (congrFun (congrFun hPE (p)) (q))).2
          dsimp only [BigradedExactCouple.initialG]
          rw [comp_eqToHom_heq_iff]
          refine dcongr_heq (HEq.refl q) ?_ (fun _ _ ↦ ?_)
          · intro q₁ q₂ h
            cases h
            simp only [hPD, hPE, Nat.cast_zero, add_zero, sub_zero]
          · refine dcongr_heq (HEq.refl p) ?_ (fun _ _ ↦ hPg)
            intro p₁ p₂ h
            cases h
            apply congrArg (fun t : ℤ → Type _ ↦ ∀ q : ℤ, t q)
            funext q
            simp only [hPD, hPE, Nat.cast_zero, add_zero, sub_zero]
        rw [hQg', hPg']
        simp only [d, e, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        rw [← Category.assoc (tD τ K p q), ← hg]
        simp only [Category.assoc]
        rfl }
  obtain ⟨⟨M, _, hM, _, hk, hd⟩, _⟩ :=
    BigradedExactCouple.derivedCoupleFunctoriality P Q T
  refine ⟨P, Q, hPE, hQE, hPD, hQD, hPa, hQa, hPf, hQf, hPg, hQg,
    hα, hg, hf, ?_, hpage⟩
  exact ⟨fun n p q ↦ (M n).tE p q, hM, fun n p q ↦ (hd n p q).symm, hk⟩

end AlgebraicGeometry.Etale
