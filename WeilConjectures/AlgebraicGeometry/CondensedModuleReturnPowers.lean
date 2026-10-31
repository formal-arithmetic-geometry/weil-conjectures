/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
import WeilConjectures.AlgebraicGeometry.CondensedModuleTransportComposition

/-! # Powers of a condensed module return at a fixed geometric point

Source: the cocycle and same-lift power steps of the condensed local-power argument.
(blueprint: lem-wf-condensed-module-return-powers).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedModule

private theorem positivePower_add {Y : Scheme.{u}} (a : Y ⟶ Y) (n m : ℕ) :
    localPositivePower a (n + m + 1) = localPositivePower a n ≫ localPositivePower a m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change localPositivePower a (n + m + 1) ≫ a =
      localPositivePower a n ≫ (localPositivePower a m ≫ a)
    rw [ih, Category.assoc]

private theorem compose_return {Y S : Scheme.{u}} (a : Y ⟶ Y) (σ : S ⟶ S)
    (z : S ⟶ Y) (n m : ℕ)
    (h₁ : z ≫ localPositivePower a n = localPositivePower σ n ≫ z)
    (h₂ : z ≫ localPositivePower a m = localPositivePower σ m ≫ z) :
    z ≫ localPositivePower a (n + m + 1) =
      localPositivePower σ (n + m + 1) ≫ z := by
  rw [positivePower_add, positivePower_add, ← Category.assoc, h₁, Category.assoc,
    h₂, ← Category.assoc]

private theorem iso_hom_mul {C : Type*} [Category C] {X : C}
    (A B R : X ≅ X) (h : B ≪≫ A = R) :
    R.hom = (End.of A.hom) * (End.of B.hom) := by
  simpa only [Iso.trans_hom, End.mul_def] using (congrArg Iso.hom h).symm

private theorem operator_add (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {Y : Scheme.{u}} (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ Y) (n m : ℕ)
    (h₁ : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    (h₂ : z ≫ localPositivePower a m =
      localPositivePower (frobeniusPointIso D).hom m ≫ z)
    (h : z ≫ localPositivePower a (n + m + 1) =
      localPositivePower (frobeniusPointIso D).hom (n + m + 1) ≫ z) :
    operator l D a M θ z (n + m + 1) h =
      operator l D a M θ z n h₁ * operator l D a M θ z m h₂ := by
  exact iso_hom_mul _ _ _ (transport_comp D l a M θ z z z n m h₁ h₂ h)

/-- Repeating one semilinear return gives powers of its actual condensed module operator.
Source: local Frobenius powers, proof steps 2--4; the composition paragraph of
`det-def-sfb-module-pushforward-pullback.proof.md`.

Proof: iterate the semilinear square to obtain the return at `d*r`. Expand the Weil-map
recursion and the specified point comparison. Pullback associativity and the mixed
reparametrization identity identify concatenation of two return words with their
composition. Induct on the positive integer `r`, grouping the word into blocks of length
`d`. The base case is the original word; the successor appends one `d`-step block and
uses the induction hypothesis and the endomorphism power recursion. Proof irrelevance
identifies the return equation proofs, so the result uses the actual `operator`, with
no choice of a different comparison.
(blueprint: lem-wf-condensed-module-return-powers). -/
theorem return_powers (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    {Y : Scheme.{u}} (a : Y ⟶ Y) (M : Modules l Y)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (z : Spec (.of D.k) ⟶ Y) (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (h : z ≫ localPositivePower a (d - 1) =
      localPositivePower (frobeniusPointIso D).hom (d - 1) ≫ z)
    (h' : z ≫ localPositivePower a (d * r - 1) =
      localPositivePower (frobeniusPointIso D).hom (d * r - 1) ≫ z) :
    operator l D a M θ z (d * r - 1) h' = operator l D a M θ z (d - 1) h ^ r := by
  have H : ∀ r : ℕ, 1 ≤ r → ∃ ht : z ≫ localPositivePower a (d * r - 1) =
      localPositivePower (frobeniusPointIso D).hom (d * r - 1) ≫ z,
      operator l D a M θ z (d * r - 1) ht = operator l D a M θ z (d - 1) h ^ r := by
    intro r
    induction r with
    | zero => intro hr; omega
    | succ r ih =>
      intro hr
      by_cases hzero : r = 0
      · subst r
        exact ⟨by simpa only [Nat.zero_add, Nat.mul_one] using h,
          by simp only [Nat.zero_add, Nat.mul_one, pow_one]⟩
      · have hr' : 1 ≤ r := by omega
        obtain ⟨ht, hpow⟩ := ih hr'
        have hmul : 1 ≤ d * r := Nat.mul_pos hd hr'
        have he : (d * r - 1) + (d - 1) + 1 = d * (r + 1) - 1 := by
          rw [Nat.mul_succ]
          omega
        have hb := compose_return a (frobeniusPointIso D).hom z (d * r - 1) (d - 1) ht h
        have hp := operator_add D l a M θ z (d * r - 1) (d - 1) ht h hb
        rw [hpow, ← pow_succ] at hp
        have hstep : ∃ ht : z ≫ localPositivePower a ((d * r - 1) + (d - 1) + 1) =
            localPositivePower (frobeniusPointIso D).hom
              ((d * r - 1) + (d - 1) + 1) ≫ z,
            operator l D a M θ z ((d * r - 1) + (d - 1) + 1) ht =
              operator l D a M θ z (d - 1) h ^ (r + 1) := ⟨hb, hp⟩
        simpa only [he] using hstep
  obtain ⟨ht, hp⟩ := H r hr
  exact hp

end WeilConjectures.CondensedModule
