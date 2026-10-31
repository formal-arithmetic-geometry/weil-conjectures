/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import all WeilConjectures.SixFunctors.Finite.Closed.FiniteClosedRealizationDomain
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.Supporting.ClosedScalarDomains
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

abbrev splitDerivedDomain (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  DerivedCategory (Sheaf (ProEt.topology T)
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))

abbrev splitScalarDomain {A B : Type u} [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B) (T : Scheme.{u}) :
    splitDerivedDomain T A ⥤ splitDerivedDomain T B :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) _ _ _ _ φ

abbrev splitExceptionalDomain (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ProEtale.sfFiniteExceptionalFixed A (Compactification.ofIsProper i)

abbrev splitCoefficientDomain (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

private theorem splitExceptionalDomain_preserves
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m : ℕ) (X Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : splitDerivedDomain X.left (splitCoefficientDomain l E m))
    (hM : finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) X.left M) :
    finiteTorConstructibleProEtaleModule l E (m + 1) (Nat.succ_pos m) Z.left
      ((splitExceptionalDomain (splitCoefficientDomain l E m) i.left).obj M) := by
  let A := splitCoefficientDomain l E m
  let := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_pos m)
  let := (Compactification.ofIsProper i.left).hasCompactification
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hunit : IsUnit (l : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) hl.symm)
  let := finiteClosed_coefficient_has_invertible_exponent l E D.k hunit (m + 1) (Nat.succ_pos m)
  have : HasInvertibleExponent (ULift.{u + 1, u} A) X.left :=
    .of_hom X.hom
  have hbc := (finiteClosed_intrinsic_bc_realization_iff l E (m + 1)
    (Nat.succ_pos m) X.left M).1 hM.1
  obtain ⟨a, b, ht⟩ := hM.2
  have hfixed : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X.left M :=
    ⟨hbc, a, b, (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
      A X.left a b ht.1 M).1 ht⟩
  have h := ProEtale.constructibleFiniteTor_rightDerivedUpperShriek
    (ULift.{u + 1, u} A) X.hom i.left hfixed
  obtain ⟨hc, c, d, htd⟩ := h
  refine ⟨(finiteClosed_intrinsic_bc_realization_iff l E (m + 1)
    (Nat.succ_pos m) Z.left _).2 hc, min c d, d, ?_⟩
  exact (ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn
    A Z.left (min c d) d (min_le_right _ _) _).2
      (ProEtale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl htd)

/-- The three finite-Tor constructibility conclusions in the closed comparison.
This is the geometric domain half of the argument; the normalized map and its
invertibility are recorded separately in `FiniteClosedShriekMapPart`.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
proof paragraph 1 (blueprint: lem-coef-finite-closed-shriek). -/
theorem finiteClosedShriek_domainPart
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (splitCoefficientDomain l E m) →+*
      ULift.{u + 1, u} (splitCoefficientDomain l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : splitDerivedDomain X.left (splitCoefficientDomain l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) X.left
      ((splitScalarDomain φ X.left).obj M) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) Z.left
      ((splitScalarDomain φ Z.left).obj
        ((splitExceptionalDomain (splitCoefficientDomain l E m) i.left).obj M)) ∧
    finiteTorConstructibleProEtaleModule l L (n + 1) (Nat.succ_pos n) Z.left
      ((splitExceptionalDomain (splitCoefficientDomain l L n) i.left).obj
        ((splitScalarDomain φ X.left).obj M)) := by
  let ψ : splitCoefficientDomain l E m →+* splitCoefficientDomain l L n :=
    ULift.ringEquiv.toRingHom.comp (φ.comp ULift.ringEquiv.symm.toRingHom)
  have hφ : ψ.ulift.{u + 1, u + 1} = φ := by
    ext x
    rfl
  obtain ⟨a, b, ht⟩ := _hM.2
  have hscalar := (closedScalarDomains_scalar D l _hl E L m n ψ X
    a b ht.1 M _hM ht).1.1
  have hNA := splitExceptionalDomain_preserves D l _hl E m X Z i M _hM
  obtain ⟨c, d, htNA⟩ := hNA.2
  have hscalarNA := (closedScalarDomains_scalar D l _hl E L m n ψ Z
    c d htNA.1 _ hNA htNA).1.1
  simp only [closedScalarExtension, hφ] at hscalar hscalarNA
  exact ⟨hscalar, hscalarNA,
    splitExceptionalDomain_preserves D l _hl L n X Z i _ hscalar⟩

end WeilConjectures
