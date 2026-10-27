/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import all Sheaf.Paper.FiniteCompactSupportConstructibility
import Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor

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
  sorry

end WeilConjectures
