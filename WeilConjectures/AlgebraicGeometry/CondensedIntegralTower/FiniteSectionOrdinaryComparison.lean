/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.GeometricTowerStatement
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.EllPowerCoefficientStages
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation

/-! # Finite section coordinates and ordinary coefficients

Source: sk-prop-sp-integral-adjunction, normalization through sk-lem-sp-reduction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

set_option maxHeartbeats 800000 in
-- Comparing both coefficient presentations unfolds their dependent scalar coordinates.
/-- The actual ell-power section categories have the ordinary finite-coefficient
constructibility predicate and compact-support functor under normalized encoding.
The same encoding is used in both assertions and for every scheme; the
constructibility assertion is for quasi-compact quasi-separated schemes.

Source: sk-prop-sp-integral-adjunction, normalization by sk-lem-sp-reduction;
finite coefficient convention of sk-def-sp-coefficient-towers
(blueprint: lem-sp-finite-section-ordinary-comparison).

Proof: the ell-power coefficient-stage theorem supplies finite discrete rings. Apply
the normalized internal/ordinary coefficient equivalence. Its constructibility and
finite-Tor clause applies to the inverse section equivalence. The existing
ordinary constructibility comparison identifies it with the fixed-module Dctf predicate.
For compact support,
cancel the section-equivalence counit on the target and then apply the ordinary
compactification comparison for the very same compactification. All maps remain natural
because they are whiskerings and composites of natural isomorphisms. No choice of a
compactification or change of quotient coordinates occurs. -/
theorem finiteSectionOrdinaryComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A := Padic.coefficientExtensionIntegers l E ⧸ ellIdeal l E ^ (n + 1)
    ∃ enc : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T,
      (∀ (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] (K), finiteCtf l E T n K ↔
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) T
          ((enc T).fixedDerived.functor.obj
            ((finiteSections l E T n).inverse.mapDerivedCategory.obj K))) ∧
      ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (c : Compactification f),
        Nonempty (finiteSupport l E c n ⋙
            (finiteSections l E Y n).inverse.mapDerivedCategory ⋙
              (enc Y).fixedDerived.functor ≅
          (finiteSections l E X n).inverse.mapDerivedCategory ⋙
            (enc X).fixedDerived.functor ⋙
              ProEtale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} (ULift.{u + 1} A)) c) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionIntegers l E ⧸ ellIdeal l E ^ (n + 1)
  have : Finite A := (ellPowerCoefficientStages l E n).1
  have : DiscreteTopology A := (ellPowerCoefficientStages l E n).2.1
  obtain ⟨enc, he, hc⟩ :=
    FiniteDiscreteOrdinary.moduleObject_ordinary_coefficient_equivalence A
  refine ⟨enc, ?_, ?_⟩
  · intro T _ _ K
    exact ((he T).2.2.2.2.1 _).trans (CondensedRing.ordinary_ctf_iff A T _)
  · intro X Y f c
    obtain ⟨e⟩ := hc X Y f c
    let s := (finiteSections l E Y n).mapDerivedCategory
    exact ⟨isoWhiskerLeft ((finiteSections l E X n).inverse.mapDerivedCategory)
      (isoWhiskerLeft
        (CondensedRing.rightDerivedLowerShriekOfCompactification (finiteRing l E n) c)
        (isoWhiskerRight s.unitIso.symm (enc Y).fixedDerived.functor) ≪≫ e)⟩

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
