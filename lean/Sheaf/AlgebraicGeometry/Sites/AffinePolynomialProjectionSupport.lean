/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.MvPolynomial.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import all Sheaf.AlgebraicGeometry.Sites.AffinePolynomialHigherProjectionSupport
import all Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound
import Sheaf.AlgebraicGeometry.Sites.PolynomialGenericStrictLocalizationField
import all Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk

/-!
# Weighted support of polynomial-projection higher direct images

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, local calculation and affine-space argument.
(blueprint: lem-sc-affine-polynomial-projection-support)
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Weighted stalk vanishing for the polynomial projection in degrees at least two.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, exceptional degree two and compactification calculation.
(blueprint: lem-sc-affine-polynomial-projection-support)

Proof: In degree two the cardinal inequality forces the base residue transcendence degree
to be at least n+1. Its strict localization is therefore the spectrum of a separably closed
field, by the polynomial generic strict-localization theorem. The finSuccEquiv coordinate
isomorphism, followed by the one-variable polynomial/affine-space isomorphism, identifies
the projection with a relative affine line. Base change to the strict localization is an
affine line over that separably closed field, of torsion cohomological dimension at most one.
The strict-henselization stalk formula, transported from derived-category cohomology to
classical rightDerived and Sheaf.H, kills degree two. For degrees greater than two use the
higher projection-support theorem, which proves the compactification Leray assembly.
Initially test at the algebraic closure of the chosen geometric field. Its unique point
covers Spec of that field; conservativity and the inverse-image/stalk comparison then
turn zero stalks into zero inverse-image sheaves. This includes n=0. -/
theorem isZero_stalk_polynomialProjection_of_lowerDimension
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hIH : ∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
      (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (m + c))
    (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)
    (q : ℕ) (hq : 2 ≤ q) :
    let f : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ⟶
        Spec (.of (MvPolynomial (Fin (n + 1)) K)) :=
      Spec.map (CommRingCat.ofHom (MvPolynomial.rename
        (Fin.succ : Fin (n + 1) → Fin (n + 2))).toRingHom)
    let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) K))),
      ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) +
          residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((Etale.upperStar AddCommGrpCat.{u + 1} s).obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj M))  := by
  classical
  dsimp only
  intro Ω _ _ s hs
  by_cases hq2 : q = 2
  · subst q
    let X := Spec (.of (MvPolynomial (Fin (n + 2)) K))
    let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
    let f : X ⟶ B := Spec.map (CommRingCat.ofHom (MvPolynomial.rename
      (Fin.succ : Fin (n + 1) → Fin (n + 2))).toRingHom)
    let b : B ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
    let t : Spec (.of (AlgebraicClosure Ω)) ⟶ B :=
      Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω))) ≫ s
    have ht : t (IsLocalRing.closedPoint (AlgebraicClosure Ω)) =
        s (IsLocalRing.closedPoint Ω) := by
      change s ((Spec.map (CommRingCat.ofHom
        (algebraMap Ω (AlgebraicClosure Ω))))
        (IsLocalRing.closedPoint (AlgebraicClosure Ω))) = _
      congr 1
      exact Subsingleton.elim _ _
    apply isZero_pointPullback_of_algClosure_stalk s
    change IsZero ((pointSmallEtale t).sheafFiber.obj ((Etale.lowerStar
      AddCommGrpCat.{u + 1} f).rightDerived 2 |>.obj M))
    have hs' : ((n + 1 : ℕ) : Cardinal.{u}) ≤ residueFieldTrdeg b
        (t (IsLocalRing.closedPoint (AlgebraicClosure Ω))) := by
      rw [ht]
      have hs'' : (2 : Cardinal.{u}) + (n : Cardinal.{u}) <
          (2 : Cardinal.{u}) + residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat, add_comm] using hs
      have hn := (Cardinal.add_lt_add_iff_of_left_lt_aleph0
        (Cardinal.natCast_lt_aleph0 (n := 2))).mp hs''
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Cardinal.natCast_add_one_le_iff).2 hn
    obtain ⟨L, hL, hLc, ⟨eR⟩⟩ := polynomial_generic_strictLocalization_field
      K (n + 1) t hs'
    let := hL
    let := hLc
    obtain ⟨e, he⟩ := polynomialProjection_affineLine_iso K (n + 1)
    have hcd := torsionCd_affineLine_pullback_of_field e f he
      (strictHenselizationStructuralMap t) L eR
    have hMt := isTorsion_of_nsmul_id_eq_zero hN hM
    have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
      (pullback.fst f (strictHenselizationStructuralMap t))).obj M) 2) :=
        hcd _ (Etale.isTorsion_upperStar _ hMt) 2 (by omega)
    obtain ⟨eH⟩ := Etale.nonempty_addEquiv_strictLocalization f (AlgebraicClosure Ω) t M hMt 2
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr eH.injective.subsingleton
  · exact isZero_stalk_polynomialProjection_of_lowerDimension_of_gt_two K n hIH
      M N hN hM q (by omega) Ω s hs


end AlgebraicGeometry.Scheme
