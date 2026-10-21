/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.AffinePolynomialInductionStep
import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension

/-!
# The affine torsion cohomological dimension bound

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md,
statement and proof (blueprint: thm-sc-affine-torsion-cd).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem subsingleton_etaleCohomology_iff_H
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) ↔
      Subsingleton (Sheaf.H F q) := open Limits in by
  obtain ⟨e⟩ := nonempty_sheafH_extDerivedIso X q
  constructor
  · intro h
    have : Subsingleton ((DerivedCategory.singleFunctor _ 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} X q).obj F) := h
    exact (e.app F).addCommGroupIsoToAddEquiv.injective.subsingleton
  · intro h
    have : Subsingleton ((Sheaf.functorH X.smallEtaleTopology q).obj F) := h
    exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

private theorem subsingleton_H_empty (X : Scheme.{u}) [IsEmpty X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H F q) := open Limits in by
  have hF : IsZero F := open Limits in by
    apply (IsZero.iff_id_eq_zero F).2
    apply (jointlyReflectIsomorphisms_ulift_pointSmallEtale X
      AddCommGrpCat.{u + 1}).jointlyFaithful.map_injective
    rintro ⟨_, ⟨x⟩⟩
    exact isEmptyElim x
  exact Sheaf.subsingleton_H_of_isZero hF q

private theorem torsionCd_of_finite
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Y) [IsFinite f] {d : ℕ}
    (hY : Y.HasTorsionCohomologicalDimensionLE d) :
    X.HasTorsionCohomologicalDimensionLE d := open Limits in by
  intro F hF q hq
  apply Etale.subsingleton_H_of_isTorsion hF q
  intro G N hN hG
  let P := Etale.lowerStar AddCommGrpCat.{u + 1} f
  have hP : (P.obj G).IsTorsion := open Limits in by
    apply isTorsion_of_nsmul_id_eq_zero hN
    calc
      N • 𝟙 (P.obj G) = P.map (N • 𝟙 G) := open Limits in by rw [Functor.map_nsmul, P.map_id]
      _ = P.map 0 := congrArg P.map hG
      _ = 0 := P.map_zero _ _
  have := hY (P.obj G) hP q hq
  exact (Etale.bijective_edgeMap_of_isFinite f G q).surjective.subsingleton

private theorem torsionCd_affine_of_polynomial
    (K : Type u) [Field K]
    (d : ℕ) (hpoly : ∀ n : ℕ, n ≤ d →
      (Spec (.of (MvPolynomial (Fin n) K))).HasTorsionCohomologicalDimensionLE n)
    (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a]
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE d := open Limits in by
  let A := Γ(X, ⊤)
  let b : Spec (.of A) ⟶ Spec (.of K) := (asIso X.toSpecΓ).inv ≫ a
  obtain ⟨φ, hφ⟩ := Spec.map_surjective b
  let : Algebra K A := φ.hom.toAlgebra
  have hb : LocallyOfFiniteType b := inferInstance
  have : Algebra.FiniteType K A := open Limits in by
    apply RingHom.finiteType_algebraMap.1
    exact HasRingHomProperty.Spec_iff.mp (hφ ▸ hb)
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : IsEmpty (Spec (.of A)) := open Limits in by
      change IsEmpty (PrimeSpectrum A)
      infer_instance
    have hzero : (Spec (.of A)).HasTorsionCohomologicalDimensionLE d :=
      fun F _ q _ ↦ subsingleton_H_empty _ F q
    exact hzero.of_isUniversalHomeomorphism (asIso X.toSpecΓ).inv
  · obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K A
    let f := Spec.map (CommRingCat.ofHom g.toRingHom)
    have hf : IsFinite f := open Limits in by
      apply (IsFinite.SpecMap_iff _).mpr
      exact hfin
    have hdim : (n : WithBot ℕ∞) ≤ d := open Limits in by
      rw [← ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin,
        ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact (IsHomeomorph.topologicalKrullDim_eq _
        X.toSpecΓ.homeomorph.isHomeomorph).ge.trans hd
    have hn : n ≤ d := open Limits in by exact_mod_cast hdim
    exact ((torsionCd_of_finite f (hpoly n hn)).mono hn).of_isUniversalHomeomorphism
      (asIso X.toSpecΓ).inv

private theorem torsionCd_affine_field_of_closed_polynomial
    (d : ℕ) (hpoly : ∀ (L : Type u) [Field L] [IsAlgClosed L] (n : ℕ), n ≤ d →
      (Spec (.of (MvPolynomial (Fin n) L))).HasTorsionCohomologicalDimensionLE n)
    (K : Type u) [Field K] (X : Scheme.{u}) [IsAffine X]
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (c : ℕ) (hK : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    X.HasTorsionCohomologicalDimensionLE (d + c) := open Limits in by
  let L := AlgebraicClosure K
  let t := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let Y := pullback a t
  have : IsAffine Y := isAffine_of_isAffineHom (pullback.fst a t)
  have hY : Y.HasTorsionCohomologicalDimensionLE d :=
    torsionCd_affine_of_polynomial L d (hpoly L) Y (pullback.snd a t)
      ((topologicalKrullDim_pullback_le_of_field a t).trans hd)
  simpa only [Nat.add_comm c d] using
    hasTorsionCohomologicalDimensionLE_add_of_isAlgClosure L a hK hY

private theorem torsionCd_polynomial_zero (K : Type u) [Field K] [IsAlgClosed K] :
    (Spec (.of (MvPolynomial (Fin 0) K))).HasTorsionCohomologicalDimensionLE 0 := open Limits in by
  let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
  exact (hasTorsionCohomologicalDimensionLE_zero_of_isSepClosed K).of_isUniversalHomeomorphism
    (Spec.map (CommRingCat.ofHom e.toRingHom))

private theorem torsionCd_polynomial_one (K : Type u) [Field K] [IsAlgClosed K] :
    (Spec (.of (MvPolynomial (Fin 1) K))).HasTorsionCohomologicalDimensionLE 1 := open Limits in by
  let a := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 1) K)))
  have : LocallyOfFiniteType a := open Limits in by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.finiteType_algebraMap.2 inferInstance
  have : IsCurve a :=
    { krullDim_le_one := open Limits in by
        change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin 1) K)) ≤ 1
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField
            (Field.toIsField K)]
        simp }
  exact (IsCurve.hasTorsionCohomologicalDimensionLE a).2 inferInstance

private theorem torsionCd_all_fields_of_polynomial_step
    (hstep : ∀ (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ),
      (∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
        (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
        ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
          [LocallyOfFiniteType a] [QuasiCompact a],
          topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
            X.HasTorsionCohomologicalDimensionLE (m + c)) →
      ∀ (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
          AddCommGrpCat.{u + 1}) (N : ℕ), 0 < N → N • 𝟙 M = 0 →
        ∀ q : ℕ, n + 2 < q → Subsingleton (Sheaf.H M q))
    (d : ℕ) :
    ∀ (K : Type u) [Field K] (c : ℕ),
      (Spec (.of K)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of K))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (d + c) := open Limits in by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro K _ c hK X _ a _ _ hd
    apply torsionCd_affine_field_of_closed_polynomial d ?_ K X a c hK hd
    intro L _ _ m hm
    rcases m with _ | m
    · exact torsionCd_polynomial_zero L
    rcases m with _ | n
    · exact torsionCd_polynomial_one L
    · intro F hF q hq
      apply Etale.subsingleton_H_of_isTorsion hF q
      intro M N hN hM
      apply hstep L n (fun K _ m c hmd hK X _ a _ _ hd ↦
        ih m (lt_of_lt_of_le hmd hm) K c hK X a hd) M N hN hM q hq

/-- An affine finite-type scheme over a field of torsion cohomological dimension at most c
has torsion cohomological dimension at most its Krull dimension plus c. On an empty scheme,
all torsion cohomology groups, including degree zero, are zero.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.md and thm-sc-affine-torsion-cd.proof.md.
(blueprint: thm-sc-affine-torsion-cd)

Proof: Compare the stated derived-category cohomology with Sheaf.H. Strongly induct on a
natural upper bound for dimension, simultaneously over every field with every available
field cohomological bound. Descend the bound from an algebraic closure using ground-field
comparison and the field-base-change dimension inequality. Over the algebraic closure,
Noether normalization supplies a finite map from each affine spectrum to polynomial space,
with the number of variables bounded by the source dimension. Bounded-exponent reduction
allows finite direct image to preserve the chosen annihilator, hence torsion. The finite
edge-map bijection transfers the polynomial-space vanishing back to the affine scheme.
Dimension-zero polynomial space is Spec of the field. Dimension one is an affine curve.
For dimension n+2 apply the polynomial induction-step theorem to the simultaneous smaller
bounds. That theorem supplies the support and Leray calculation for the polynomial
projection, including the punctured coefficient-field calculation at infinity.
An affine finite-type scheme has finite Krull dimension. For a nonempty scheme its dimension
is nonnegative, so the natural-number conversion in this statement is that finite dimension;
apply the simultaneous bound with it. For an empty scheme geometric points detect the zero
sheaf, hence every cohomology group is zero without any positive-degree restriction. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_isAffine
    (K : Type u) [Field K] (c : ℕ)
    (hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c)
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    (Nonempty X → HasTorsionEtaleCohomologicalDimensionLE X
      (((topologicalKrullDim X).unbotD 0).toNat + c)) ∧
    (IsEmpty X → ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsTorsion → ∀ q : ℕ,
        Subsingleton ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := open Limits in by
  constructor
  · intro _
    obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of K))
    have hfinite : (topologicalKrullDim X).unbotD 0 ≠ ⊤ := open Limits in by
      apply ne_top_of_le_ne_top (show (d : ℕ∞) ≠ ⊤ by simp)
      exact (WithBot.unbotD_le_iff (by simp)).2 hd
    have hdim : topologicalKrullDim X ≤
        ((((topologicalKrullDim X).unbotD 0).toNat : ℕ) : WithBot ℕ∞) := open Limits in by
      change topologicalKrullDim X ≤
        ((((topologicalKrullDim X).unbotD 0).toNat : ℕ∞) : WithBot ℕ∞)
      rw [ENat.natCast_toNat hfinite]
      exact WithBot.le_coe_unbotD _ _
    have hK' : (Spec (.of K)).HasTorsionCohomologicalDimensionLE c :=
      fun F hF q hq ↦ (subsingleton_etaleCohomology_iff_H F q).mp (hK F hF q hq)
    have hX := torsionCd_all_fields_of_polynomial_step
      subsingleton_H_polynomial_of_lowerDimension
      ((topologicalKrullDim X).unbotD 0).toNat K c hK' X (X ↘ Spec (.of K)) hdim
    intro F hF q hq
    exact (subsingleton_etaleCohomology_iff_H F q).mpr (hX F hF q hq)
  · intro h F _ q
    let := h
    exact (subsingleton_etaleCohomology_iff_H F q).mpr (subsingleton_H_empty X F q)

end AlgebraicGeometry.Scheme

end
