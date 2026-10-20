/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import WeilConjectures.ConstructibleSheaf.Refinement

/-!
# Finite fibre-product refinement of scheme stratifications

Source: finite-reductions Step 6, Stacks Project Tags 054I, 02V0 and 005H.
(blueprint: lem-sfb-finite-stratification-wide-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The factors of the common fibre product, including the common open itself.
Source: finite-reductions Step 6.
(blueprint: lem-sfb-finite-stratification-wide-pullback). -/
def stratificationWideFactors {X : Scheme.{u}} {r : ℕ} (U : X.Opens)
    (O : Fin r → X.Opens) (S : ∀ j, Stratification (O j).toScheme)
    (a : ∀ j, Fin (S j).n) : Option (Fin r) → Scheme.{u}
  | none => U.toScheme
  | some j => (S j).domain (a j)

/-- The given factor maps to the common ambient scheme.
Source: finite-reductions Step 6.
(blueprint: lem-sfb-finite-stratification-wide-pullback). -/
def stratificationWideArrows {X : Scheme.{u}} {r : ℕ} (U : X.Opens)
    (O : Fin r → X.Opens) (S : ∀ j, Stratification (O j).toScheme)
    (a : ∀ j, Fin (S j).n) : ∀ t, stratificationWideFactors U O S a t ⟶ X
  | none => U.ι
  | some j => (S j).immersion (a j) ≫ (O j).ι

private def identityStratification (Y : Scheme.{u}) : Stratification Y where
  n := 1
  stratum _ := Set.univ
  isLocallyClosed_stratum _ := isClosed_univ.isLocallyClosed
  isConstructible_stratum _ := Topology.IsConstructible.univ
  iUnion_stratum_eq_univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, exists_const]
  pairwise_disjoint_stratum := by intro i j h; exact (h (Subsingleton.elim i j)).elim
  domain _ := Y
  immersion _ := 𝟙 Y
  range_immersion _ := by simp

private structure WideRefinement {X : Scheme.{u}} {r : ℕ} (U : X.Opens)
    (O : Fin r → X.Opens) (S : ∀ j, Stratification (O j).toScheme) where
  T : Stratification U.toScheme
  a : Fin T.n → ∀ j, Fin (S j).n
  c : ∀ k, WidePullbackCone (stratificationWideArrows U O S (a k))
  hp : ∀ k, (c k).pt = T.domain k
  hto : ∀ k, eqToHom (hp k).symm ≫ (c k).π none = T.immersion k
  hl : ∀ k, IsLimit (c k)
  he : r = 0 → T.n = 1 ∧ ∀ k, IsIso (T.immersion k)

private theorem wideRefinement_exists {X : Scheme.{u}} (r : ℕ) (U : X.Opens)
    (O : Fin r → X.Opens) (S : ∀ j, Stratification (O j).toScheme)
    (hU : ∀ j, U ≤ O j) : Nonempty (WideRefinement U O S) := by
  classical
  induction r with
  | zero =>
    let T := identityStratification U.toScheme
    let a : Fin T.n → ∀ j : Fin 0, Fin (S j).n := fun _ j ↦ Fin.elim0 j
    let c (k : Fin T.n) : WidePullbackCone (stratificationWideArrows U O S (a k)) :=
      WidePullbackCone.mk U.ι (fun t ↦ match t with
        | none => 𝟙 U.toScheme
        | some j => Fin.elim0 j) (by
          intro t
          cases t with
          | none => exact Category.id_comp _
          | some j => exact Fin.elim0 j)
    refine ⟨⟨T, a, c, fun _ ↦ rfl, ?_, ?_, ?_⟩⟩
    · intro k; exact Category.comp_id _
    · intro k
      refine WidePullbackCone.IsLimit.mk _ (fun t ↦ t.π none) ?_ ?_ ?_
      · intro t; exact t.condition none
      · intro t i
        cases i with
        | none => exact Category.comp_id _
        | some j => exact Fin.elim0 j
      · intro t m hm hπ
        have hh := hπ none
        change m ≫ 𝟙 U.toScheme = t.π none at hh
        exact (Category.comp_id m).symm.trans hh
    · intro _; exact ⟨rfl, fun _ ↦ inferInstanceAs (IsIso (𝟙 U.toScheme))⟩
  | succ r ih =>
    obtain ⟨Q⟩ := ih (fun j ↦ O j.succ) (fun j ↦ S j.succ) (fun j ↦ hU j.succ)
    let f : U.toScheme ⟶ (O 0).toScheme := X.homOfLE (hU 0)
    let A := (S 0).pullback f
    let T := Q.T.inter A
    let i (k : Fin T.n) : Fin Q.T.n := (finProdFinEquiv.symm k).1
    let j (k : Fin T.n) : Fin (S 0).n := (finProdFinEquiv.symm k).2
    let a (k : Fin T.n) : ∀ l : Fin (r + 1), Fin (S l).n :=
      Fin.cases (j k) (fun l ↦ Q.a (i k) l)
    let q (k : Fin T.n) : T.domain k ⟶ Q.T.domain (i k) := pullback.fst _ _
    let b (k : Fin T.n) : T.domain k ⟶ A.domain (j k) := pullback.snd _ _
    let head (k : Fin T.n) : T.domain k ⟶ (S 0).domain (j k) :=
      b k ≫ pullback.fst _ _
    let old (k : Fin T.n) (l : Option (Fin r)) :
        T.domain k ⟶ stratificationWideFactors U (fun t ↦ O t.succ)
          (fun t ↦ S t.succ) (Q.a (i k)) l :=
      q k ≫ eqToHom (Q.hp (i k)).symm ≫ (Q.c (i k)).π l
    have hu (k : Fin T.n) : old k none = T.immersion k := by
      dsimp only [old]
      rw [← Category.assoc, Category.assoc, Q.hto]
      rfl
    have hh (k : Fin T.n) : head k ≫
        ((S 0).immersion (j k) ≫ (O 0).ι) = T.immersion k ≫ U.ι := by
      dsimp only [head]
      rw [Category.assoc, ← Category.assoc (pullback.fst _ _), pullback.condition,
        Category.assoc]
      change b k ≫ (pullback.snd _ _ ≫ (f ≫ (O 0).ι)) = _
      rw [show f ≫ (O 0).ι = U.ι from X.homOfLE_ι (hU 0)]
      change (b k ≫ A.immersion (j k)) ≫ U.ι = _
      rw [show b k ≫ A.immersion (j k) =
        q k ≫ Q.T.immersion (i k) from pullback.condition.symm]
      rfl
    let π (k : Fin T.n) : ∀ l : Option (Fin (r + 1)),
        T.domain k ⟶ stratificationWideFactors U O S (a k) l
      | none => T.immersion k
      | some l => Fin.cases (head k) (fun t ↦ old k (some t)) l
    let c (k : Fin T.n) : WidePullbackCone (stratificationWideArrows U O S (a k)) :=
      WidePullbackCone.mk (T.immersion k ≫ U.ι) (π k) (by
        intro l
        cases l with
        | none => rfl
        | some l =>
          refine Fin.cases ?_ (fun t ↦ ?_) l
          · exact hh k
          · dsimp [π, stratificationWideArrows, a, old]
            have hc := (Q.c (i k)).condition (some t)
            change (Q.c (i k)).π (some t) ≫
              ((S t.succ).immersion (Q.a (i k) t) ≫ (O t.succ).ι) = _ at hc
            rw [Category.assoc, Category.assoc, hc]
            rw [← (Q.c (i k)).condition none]
            change old k none ≫ U.ι = _
            rw [hu])
    refine ⟨⟨T, a, c, fun _ ↦ rfl, ?_, ?_, ?_⟩⟩
    · intro k; exact Category.id_comp _
    · intro k
      let liftOld (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          t.pt ⟶ Q.T.domain (i k) :=
        (Q.hl (i k)).lift (WidePullbackCone.mk t.base
          (fun l ↦ match l with
            | none => t.π none
            | some l => t.π (some l.succ)) (by
              intro l
              cases l with
              | none => exact t.condition none
              | some l => exact t.condition (some l.succ))) ≫ eqToHom (Q.hp (i k))
      have liftOld_π (t : WidePullbackCone (stratificationWideArrows U O S (a k)))
          (l : Option (Fin r)) :
          liftOld t ≫ eqToHom (Q.hp (i k)).symm ≫ (Q.c (i k)).π l =
            (match l with | none => t.π none | some l => t.π (some l.succ)) := by
        dsimp only [liftOld]
        rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        exact (Q.hl (i k)).fac _ (some l)
      have liftOld_to (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          liftOld t ≫ Q.T.immersion (i k) = t.π none := by
        rw [← Q.hto]
        exact liftOld_π t none
      let liftA (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          t.pt ⟶ A.domain (j k) :=
        pullback.lift (t.π (some 0)) (t.π none) (by
          apply (cancel_mono (O 0).ι).1
          simp only [Category.assoc]
          rw [show f ≫ (O 0).ι = U.ι from X.homOfLE_ι (hU 0)]
          exact (t.condition (some 0)).trans (t.condition none).symm)
      let lift (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          t.pt ⟶ T.domain k :=
        pullback.lift (liftOld t) (liftA t) (by
          change liftOld t ≫ Q.T.immersion (i k) = liftA t ≫ pullback.snd _ _
          rw [liftOld_to]
          simp only [liftA, pullback.lift_snd])
      have lift_q (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          lift t ≫ q k = liftOld t := pullback.lift_fst _ _ _
      have lift_b (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          lift t ≫ b k = liftA t := pullback.lift_snd _ _ _
      have lift_to (t : WidePullbackCone (stratificationWideArrows U O S (a k))) :
          lift t ≫ T.immersion k = t.π none := by
        change lift t ≫ (q k ≫ Q.T.immersion (i k)) = _
        rw [← Category.assoc, lift_q, liftOld_to]
      refine WidePullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
      · intro t
        change lift t ≫ (T.immersion k ≫ U.ι) = t.base
        rw [← Category.assoc, lift_to]
        exact t.condition none
      · intro t l
        cases l with
        | none => exact lift_to t
        | some l =>
          refine Fin.cases ?_ (fun l ↦ ?_) l
          · change lift t ≫ (b k ≫ pullback.fst _ _) = t.π (some 0)
            rw [← Category.assoc, lift_b]
            exact pullback.lift_fst _ _ _
          · change lift t ≫ (q k ≫ eqToHom (Q.hp (i k)).symm ≫
              (Q.c (i k)).π (some l)) = _
            rw [← Category.assoc, lift_q]
            exact liftOld_π t (some l)
      · intro t m hm hπ
        apply pullback.hom_ext
        · apply (cancel_mono (Q.T.immersion (i k))).1
          rw [Category.assoc, lift_q, liftOld_to]
          exact hπ none
        · apply (cancel_mono (A.immersion (j k))).1
          change m ≫ b k ≫ A.immersion (j k) = lift t ≫ b k ≫ A.immersion (j k)
          rw [← pullback.condition]
          change m ≫ q k ≫ Q.T.immersion (i k) =
            lift t ≫ q k ≫ Q.T.immersion (i k)
          exact congrArg (fun z ↦ z ≫ Q.T.immersion (i k))
            (show m ≫ q k = lift t ≫ q k by
              apply (cancel_mono (Q.T.immersion (i k))).1
              rw [Category.assoc, lift_q, liftOld_to]
              exact hπ none)
    · intro h; omega

/-- Intersect finitely many finite constructible partitions by actual fibre products.
Source: finite-reductions Step 6, Stacks Tags 054I, 02V0 and 005H.
(blueprint: lem-sfb-finite-stratification-wide-pullback).

Proof: first pull each partition back from O j to U. Induct on the finite set of
partitions. Start with the identity stratum of U. At the induction step pull the
next partition back to every current stratum and compose the immersions. The image
of each composite is the intersection of its two images: the first immersion is
injective and the pullback projection has the inverse-image range. Thus the images
are locally closed, constructible, pairwise disjoint and cover U. The finite product
of the finite index sets indexes these strata. Delete the empty schemes when r is
nonzero, and enumerate the remaining finite index set by Fin n. Pasting the
pullback universal properties gives a limiting wide-pullback cone with every
original stratum as a factor. Its projection to U is the composite immersion. For
r = 0 the identity stratum and its singleton-factor cone already have the required
universal property, including when U is empty. No sheaves or coefficients enter. -/
theorem finite_stratification_wide_pullback {X : Scheme.{u}} (r : ℕ) (U : X.Opens)
    (O : Fin r → X.Opens) (S : ∀ j, Stratification (O j).toScheme)
    (hU : ∀ j, U ≤ O j) :
    ∃ (T : Stratification U.toScheme)
      (a : Fin T.n → ∀ j, Fin (S j).n)
      (c : ∀ k, WidePullbackCone (stratificationWideArrows U O S (a k)))
      (hp : ∀ k, (c k).pt = T.domain k),
      (∀ k, eqToHom (hp k).symm ≫ (c k).π none = T.immersion k) ∧
      (∀ k, Nonempty (IsLimit (c k))) ∧
      (r ≠ 0 → ∀ k, Nonempty (T.domain k)) ∧
      (r = 0 → T.n = 1 ∧ ∀ k, IsIso (T.immersion k)) := by
  classical
  obtain ⟨Q⟩ := wideRefinement_exists r U O S hU
  by_cases hr : r = 0
  · exact ⟨Q.T, Q.a, Q.c, Q.hp, Q.hto, fun k ↦ ⟨Q.hl k⟩,
      fun h ↦ (h hr).elim, fun _ ↦ Q.he hr⟩
  · let I := {k : Fin Q.T.n // Nonempty (Q.T.domain k)}
    let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
    let idx (k : Fin (Fintype.card I)) : Fin Q.T.n := (e k).val
    let T : Stratification U.toScheme :=
      { n := Fintype.card I
        stratum k := Q.T.stratum (idx k)
        isLocallyClosed_stratum k := Q.T.isLocallyClosed_stratum _
        isConstructible_stratum k := Q.T.isConstructible_stratum _
        iUnion_stratum_eq_univ := by
          apply Set.eq_univ_of_forall
          intro x
          obtain ⟨k, hk⟩ := Set.mem_iUnion.mp
            (Q.T.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
          have hn : Nonempty (Q.T.domain k) := by
            rw [← Q.T.range_immersion] at hk
            obtain ⟨y, _⟩ := hk
            exact ⟨y⟩
          refine Set.mem_iUnion.mpr ⟨e.symm ⟨k, hn⟩, ?_⟩
          simpa only [idx, Equiv.apply_symm_apply] using hk
        pairwise_disjoint_stratum := by
          intro k l h
          apply Q.T.pairwise_disjoint_stratum
          intro hkl
          exact h (e.injective (Subtype.ext hkl))
        domain k := Q.T.domain (idx k)
        immersion k := Q.T.immersion (idx k)
        range_immersion k := Q.T.range_immersion _ }
    exact ⟨T, fun k ↦ Q.a (idx k), fun k ↦ Q.c (idx k), fun k ↦ Q.hp (idx k),
      fun k ↦ Q.hto (idx k), fun k ↦ ⟨Q.hl (idx k)⟩,
      fun _ k ↦ (e k).property, fun h ↦ (hr h).elim⟩

end AlgebraicGeometry.Scheme
