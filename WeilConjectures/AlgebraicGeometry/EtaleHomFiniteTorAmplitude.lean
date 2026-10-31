/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Derived internal Hom at finite coefficients on the etale site

Source: Weil conjectures blueprint, sec-six-functors/sk-thm-sf-hom-ctf,
node thm-sf-hom-ctf, order 2199 (blueprint: thm-sf-hom-ctf).
The current main-20261015 snapshot has the same theorem at order 2543.

The finite-Tor constructible predicate is the recorded etale presentation. The coefficient
ring has its canonical universe lift. Internal Hom and site-perfectness use the existing
etale module-sheaf interfaces: local models are bounded complexes of retracts of finite
free constant module sheaves. No separatedness of the structure morphism is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

-- Align the lifted coefficient Ring instance with the generic CommRing theorem.
attribute [local instance 2000] CommRing.toRing

private theorem boundedConstructible_iff
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Etale.DerivedCategoryModule A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 (fun i hi ↦ hz i (.inl hi))
    · exact (_root_.DerivedCategory.isLE_iff K b).2 (fun i hi ↦ hz i (.inr hi))
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb i hi

private theorem coefficient_invertibleExponent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    HasInvertibleExponent (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      (Spec (.of D.k)) := by
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hlk : (l : D.k) ≠ 0 := fun hz ↦
    hl ((CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm.trans
      (ringChar.eq D.k D.p))
  have hu : IsUnit ((l ^ n : ℕ) : D.k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow n
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · exact ULift.down_injective hkill
  · simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom


/-- Internal Hom preserves finite-Tor bounded constructibility, with a dimension-dependent
Tor interval and the sharper interval when the first argument is site-perfect.
Source: Weil blueprint, thm-sf-hom-ctf, order 2199 (blueprint: thm-sf-hom-ctf).

Proof:
1. The coefficient ring. The finite base field has characteristic p (its cardinality is a
power of p), and so has its algebraic closure k. The extension absolute value gives |l| < 1,
so by lem-weil-l-adic-extension-integers-dvr l lies in the maximal ideal generated by the
uniformizer; hence l^n = 0 in A = A_{E,n}. As l differs from p, l^n is a unit of k and of the
global sections of Spec k. This is HasInvertibleExponent for the lifted ring, pulled back to X.
2. The predicates. The finite-ring comparison of constructible etale module sheaves
(lem-weil-pbc-constructible-etale-module-sheaf-comparison) identifies isBoundedConstructible
with boundedConstructible (bounds via isGE_iff/isLE_iff, lower endpoint min a b in the
reverse direction); hasTorAmplitudeIn is equivalent to torAmplitudeIn.
3. General case. The proved source theorems Etale.boundedConstructible_derivedHom and
Etale.torAmplitudeIn_derivedHom (the unit's declarations) give bounded constructibility and
the interval [c-b-2m,d-a+2m]: a finite affine cover by separated finite-type charts of
dimension at most m (lem-weil-pbc-affine-source-morphism-separated,
lem-weil-pbc-open-subspace-dimension-monotone, lem-weil-pbc-finite-type-over-noetherian) and
cor-weil-finite-constructible-hom (Verdier biduality) on each chart.
4. Site-perfect case. IsSitePerfect.isDualizable (lem-sf-source-etale-site-perfect-dualizable)
makes K dualizable; its dual has Tor interval [-b,-a] and RHom(K,M) is its derived tensor
with M, so Etale.torAmplitudeIn_derivedHom_of_isDualizable_aux gives [c-b,d-a].
5. From a <= b, c <= d and m >= 0, c-b-2m <= d-a+2m, which witnesses finite Tor amplitude in
the first conclusion. -/
theorem finiteCoefficient_derivedHom_ctf_etale
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (m : ℕ) (_hm : topologicalKrullDim X ≤ (m : WithBot ℕ∞))
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : finiteTorConstructibleEtale l E n hn X K)
    (_hM : finiteTorConstructibleEtale l E n hn X M)
    (_hKt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hMt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X c d M) :
    finiteTorConstructibleEtale l E n hn X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (c - b - 2 * (m : ℤ)) (d - a + 2 * (m : ℤ))
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    (Etale.DerivedCategory.IsSitePerfect K →
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X (c - b) (d - a)
        (((Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M)) := by
  let : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : HasInvertibleExponent A (Spec (.of D.k)) :=
    coefficient_invertibleExponent D l _hl E n
  let : HasInvertibleExponent A X := .of_hom (X ↘ Spec (.of D.k))
  have hK := (boundedConstructible_iff A X K).1 _hK.1
  have hM := (boundedConstructible_iff A X M).1 _hM.1
  have hKt := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 _hKt
  have hMt := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 _hMt
  have hc := Etale.boundedConstructible_derivedHom A (X ↘ Spec (.of D.k))
    a b c d hK hKt hM hMt
  have ht := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (Etale.torAmplitudeIn_derivedHom A (X ↘ Spec (.of D.k)) m _hm
      a b c d hK hKt hM hMt)
  refine ⟨⟨(boundedConstructible_iff A X _).2 hc,
    c - b - 2 * (m : ℤ), d - a + 2 * (m : ℤ), by omega, ht⟩, ht, ?_⟩
  intro hp
  exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (Etale.torAmplitudeIn_derivedHom_of_isDualizable_aux (ModuleCat.{u + 1} A)
      hKt hp.isDualizable hMt)

end WeilConjectures
