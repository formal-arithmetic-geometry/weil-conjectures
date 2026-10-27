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

variable {A B : Type u} [CommRing A] [CommRing B]

abbrev splitCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :=
  Padic.coefficientExtensionRing l E (n + 1)

abbrev splitDerived (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))

abbrev splitScalar {A B : Type u} [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B) (T : Scheme.{u}) :
    splitDerived T A ⥤ splitDerived T B :=
  @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) _ _ _ _ φ

abbrev splitPush (A : Type u) [CommRing A] {Z X : Scheme.{u}} (i : Z ⟶ X) :
    splitDerived Z A ⥤ splitDerived X A :=
  (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).rightDerivedFunctor

abbrev splitExceptional (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  ProEtale.sfFiniteExceptionalFixed A (Compactification.ofIsProper i)

def splitCounit (A : Type u) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : splitDerived X A) :
    (splitPush A i).obj ((splitExceptional A i).obj M) ⟶ M := by
  letI := (Compactification.ofIsProper i).hasCompactification
  exact
    open Classical in
    if hX : CompactSpace X then
      letI := hX
      if hM : DerivedCategory.TStructure.t.plus M then
        (ProEtale.rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).inv.app _ ≫
          ProEtale.rightDerivedUpperShriekCounit i M hM
      else 0
    else 0

def splitDirectInverse {A B : Type u} [CommRing A] [CommRing B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) (N : splitDerived Z A) :
    (splitPush B i).obj ((splitScalar φ Z).obj N) ⟶
      (splitScalar φ X).obj ((splitPush A i).obj N) :=
  open Classical in
  if h : IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) then
    @inv _ _ _ _ (ProEtale.finiteCoefficientChangeDirectImageMap φ i N) h
  else 0

def splitIsMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : splitDerived X A)
    (b : (splitScalar φ Z).obj ((splitExceptional A i).obj M) ⟶
      (splitExceptional B i).obj ((splitScalar φ X).obj M)) : Prop :=
  (splitPush B i).map b ≫
      splitCounit B i ((splitScalar φ X).obj M) =
    splitDirectInverse φ i ((splitExceptional A i).obj M) ≫
      (splitScalar φ X).map (splitCounit A i M)

def splitMap [Finite A] [Finite B]
    (φ : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : splitDerived X A) :
    (splitScalar φ Z).obj ((splitExceptional A i).obj M) ⟶
      (splitExceptional B i).obj ((splitScalar φ X).obj M) :=
  open Classical in
  if h : ∃! b, splitIsMap φ i M b then h.exists.choose else 0

/-- The counit-normalized map and its ordinary direct-image comparison are the
strictly algebraic part of the closed coefficient argument. The geometric finite-
Tor domain assertions are recorded separately in `FiniteClosedShriekDomainPart`.
Source: blueprint sec-six-functors/sk-prop-sf-biduality-general, order 2139,
proof paragraph 2 (blueprint: lem-coef-finite-closed-shriek). -/
theorem finiteClosedShriek_mapPart
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (m n : ℕ)
    (φ : ULift.{u + 1, u} (splitCoefficient l E m) →+*
      ULift.{u + 1, u} (splitCoefficient l L n))
    (X Z : Over (Spec (CommRingCat.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (M : splitDerived X.left (splitCoefficient l E m))
    (_hM : finiteTorConstructibleProEtaleModule l E (m + 1)
      (Nat.succ_pos m) X.left M) :
    (∃! b, splitIsMap φ i.left M b) ∧
    splitIsMap φ i.left M (splitMap φ i.left M) ∧
    IsIso (ProEtale.finiteCoefficientChangeDirectImageMap φ i.left
      ((splitExceptional (splitCoefficient l E m) i.left).obj M)) ∧
    IsIso (splitMap φ i.left M) := by
  sorry

end WeilConjectures
