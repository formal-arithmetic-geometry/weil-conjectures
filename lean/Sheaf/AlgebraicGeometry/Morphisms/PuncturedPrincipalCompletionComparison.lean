/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Sheaf.RingTheory.Depth
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalFiniteLevelLift
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalRestrictionKernel

/-! # Formal sections as an element of the principal adic completion

Source: Stacks Project, Tags 0BLD, 0AVY and 0BK0.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev scalarRestriction {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (W : (Spec (.of R)).Opens) (n : ℕ) :
    R →+* Γ(FiniteEtale.Adic.openThickening f W n, ⊤) :=
  ((ΓSpecIso (.of R)).inv ≫
    (FiniteEtale.Adic.openThickeningMap f W n ≫ W.ι).appTop).hom

private theorem scalarRestriction_transition {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (W : (Spec (.of R)).Opens) (n : ℕ) (a : R) :
    (FiniteEtale.Adic.openThickeningTransition f W n).appTop
      (scalarRestriction f W (n + 1) a) = scalarRestriction f W n a := by
  change (((ΓSpecIso (.of R)).inv ≫
    (FiniteEtale.Adic.openThickeningMap f W (n + 1) ≫ W.ι).appTop) ≫
      (FiniteEtale.Adic.openThickeningTransition f W n).appTop) a = _
  rw [Category.assoc, ← Scheme.Hom.comp_appTop]
  congr 2
  simp [FiniteEtale.Adic.openThickeningTransition, FiniteEtale.Adic.openThickeningMap]

private theorem scalarRestriction_quotient {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (W : (Spec (.of R)).Opens) (n : ℕ) (a : R) :
    ((ΓSpecIso (.of (R ⧸ (RingHom.ker f) ^ (n + 1)))).inv ≫
      (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
        (Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1)) a) =
      scalarRestriction f W n a := by
  change (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker f) ^ (n + 1))) ≫
    (ΓSpecIso (.of (R ⧸ (RingHom.ker f) ^ (n + 1)))).inv ≫
      (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop) a = _
  rw [← Category.assoc, ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.Hom.comp_appTop]
  change ((ΓSpecIso (.of R)).inv ≫
    (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n) ≫
      FiniteEtale.Adic.baseMap f n).appTop) a = _
  rw [← pullback.condition]

/-- On a depth-three puncture, formal sections determine an element of the
principal adic completion, even when the local ring is not complete.

Source: Stacks Project, Tag 0BLD (Lemma 52.3.2, p = 0), as used in Tag 0EII;
Tags 0AVY and 0BK0.
(blueprint: lem-sbc-punctured-principal-completion-comparison)

Proof: Write I = (g), X = Spec R and U = X minus the closed point.
Depth at least three makes H^i_m(R) vanish for i = 0, 1, 2 (0AVY).
The exact sequence of 0BK0 therefore identifies R with Gamma(U,O_U),
by the canonical restriction map, and identifies H^1(U,O_U) with zero.
The kernels of multiplication by successive powers of g on O_U stabilize:
they are restrictions of the ascending annihilator ideals of g^n in R,
which stabilize because R is Noetherian. Apply 0BLD with F = O_U and p = 0.
Its top exact row identifies the ordinary I-adic completion of Gamma(U,O_U)
with lim Gamma(U,O_U/g^n), since the Tate module of H^1(U,O_U) is zero.
Through the canonical identification Gamma(U,O_U) = R, this is AdicCompletion I R.
The kernel of R -> R/(g) is I. The pullback defining openThickening is the open
subscheme of Spec(R/I^(n+1)) over U. Pushforward along this closed immersion
identifies its structure sheaf with O_U/g^(n+1)O_U. Its sections therefore
are the terms in the preceding inverse limit. The quotient transition maps
are openThickeningTransition, by the pullback identities. The comparison
from the completion is obtained by evaluating at n+1, using Gamma(Spec R/I^(n+1))
= R/I^(n+1), and restricting along pullback.snd. This gives exactly the formula
below. Omitting index zero does not change the limit, since R/I^0 is zero.
Existence and uniqueness now follow from the comparison isomorphism.
For g=0 the system is constant; for nilpotent g it is eventually constant.
No regularity of g or completeness of R is required. -/
theorem punctured_principal_completion_comparison
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let I := RingHom.ker f
    ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f W n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f W n).appTop
        (s (n + 1)) = s n) →
      ∃! q : AdicCompletion I R, ∀ n,
        ((ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
          (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
            (AdicCompletion.evalₐ I (n + 1) q) = s n := by
  classical
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let I := RingHom.ker f
  intro s hs
  choose b hb using punctured_principal_finite_level_lift R g hg hdepth W hW s hs
  choose k hk hker using punctured_principal_restriction_kernel R g hg hdepth W hW
  change ∀ n, scalarRestriction f W n (b n) = s n at hb
  change ∀ n a b, scalarRestriction f W (k n) a = scalarRestriction f W (k n) b →
    a - b ∈ I ^ (n + 1) at hker
  have hdown (n m : ℕ) (hnm : n ≤ m) (a : R)
      (ha : scalarRestriction f W m a = s m) : scalarRestriction f W n a = s n := by
    induction m, hnm using Nat.le_induction with
    | base => exact ha
    | succ m hnm ih =>
      apply ih
      rw [← scalarRestriction_transition f W m a, ha, hs]
  let a : ℕ → R := fun n ↦ b (k n)
  have ha (n : ℕ) : scalarRestriction f W n (a n) = s n :=
    hdown n (k n) (hk n) _ (hb (k n))
  have hcoh (n m : ℕ) (hnm : n ≤ m) :
      Ideal.Quotient.mk (I ^ (n + 1)) (a n) =
        Ideal.Quotient.mk (I ^ (n + 1)) (a m) := by
    let j := max (k n) (k m)
    have hn : a n - b j ∈ I ^ (n + 1) := by
      apply hker n
      exact (hb (k n)).trans
        (hdown (k n) j (Nat.le_max_left _ _) _ (hb j)).symm
    have hm : a m - b j ∈ I ^ (m + 1) := by
      apply hker m
      exact (hb (k m)).trans
        (hdown (k m) j (Nat.le_max_right _ _) _ (hb j)).symm
    have hm' := (Ideal.pow_le_pow_right (Nat.succ_le_succ hnm) :
      I ^ (m + 1) ≤ I ^ (n + 1)) hm
    exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hn).trans
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hm').symm
  let A : AdicCompletion.AdicCauchySequence I R :=
    AdicCompletion.AdicCauchySequence.mk I R a (fun n ↦ by
      apply SModEq.sub_mem.mpr
      have h := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
        (hcoh n (n + 1) (Nat.le_succ n))
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
        (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n) h)
  let q := AdicCompletion.mk I R A
  have hq (n : ℕ) :
      ((ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv ≫
        (pullback.snd W.ι (FiniteEtale.Adic.baseMap f n)).appTop)
          (AdicCompletion.evalₐ I (n + 1) q) = s n := by
    rw [AdicCompletion.evalₐ_mk]
    rw [scalarRestriction_quotient]
    exact hdown n (n + 1) (Nat.le_succ n) _ (ha (n + 1))
  refine ⟨q, hq, ?_⟩
  intro r hr
  obtain ⟨B, rfl⟩ := AdicCompletion.mk_surjective I R r
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
    have : Subsingleton (R ⧸ I ^ 0) := by
      simp only [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact Subsingleton.elim _ _
  | succ n =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    have hB : scalarRestriction f W (k n) (B (k n + 1)) = s (k n) := by
      have h := hr (k n)
      change ((ΓSpecIso (.of (R ⧸ I ^ (k n + 1)))).inv ≫
        (pullback.snd W.ι (FiniteEtale.Adic.baseMap f (k n))).appTop)
          (AdicCompletion.evalₐ I (k n + 1) (AdicCompletion.mk I R B)) = s (k n) at h
      rw [AdicCompletion.evalₐ_mk, scalarRestriction_quotient] at h
      exact h
    have hmem : B (k n + 1) - a n ∈ I ^ (n + 1) := by
      apply hker n
      exact hB.trans (hb (k n)).symm
    have hBc : Ideal.Quotient.mk (I ^ (n + 1)) (B (n + 1)) =
        Ideal.Quotient.mk (I ^ (n + 1)) (B (k n + 1)) := by
      have h := B.property (Nat.succ_le_succ (hk n))
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp h
    exact hBc.trans (((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hmem).trans
      (hcoh n (n + 1) (Nat.le_succ n)))

end AlgebraicGeometry.Scheme
