/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.WitnessCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.Compactification.Affine

/-! # Ordinary finiteness of closed exceptional dualizing objects

Source: lem-coef-finite-dualizing.proof.md, paragraph 3, ordinary etale inputs.
(blueprint: lem-coef-closed-dualizing-etale-finiteness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The four ordinary bounded constructible finite-Tor inputs, before site transport.
Source: lem-coef-finite-dualizing.proof.md, paragraph 3
(blueprint: lem-coef-closed-dualizing-etale-finiteness). -/
def closedDualizingEtaleFinitenessProperty
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (r : ℕ)
    (Y : Scheme.{u}) [IsAffine Y]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))) [IsClosedImmersion i] : Prop :=
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  let B := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E m)
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n (hm.trans hmn)
  letI : Finite (Padic.coefficientExtensionRing l E m) :=
    Padic.finite_coefficientExtensionRing l E m hm
  let φ : A →+* B := RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))
  let P := AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))
  let aP := P ↘ Spec (.of D.k)
  let c := Compactification.ofIsProper i
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification B c
  let IA := (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1, u + 1} A)
    c).rightAdjoint
  let IB := (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1, u + 1} B)
    c).rightAdjoint
  let M := Etale.dualizingComplex A aP
  let MB := (pbcFixedScalarExtension P.smallEtaleTopology φ).obj M
  let N := IA.obj M
  (Etale.DerivedCategory.isBoundedConstructible A P ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A P a b K)) M ∧
  (Etale.DerivedCategory.isBoundedConstructible A Y ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn A Y a b K)) N ∧
  (Etale.DerivedCategory.isBoundedConstructible B P ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn B P a b K)) MB ∧
  (Etale.DerivedCategory.isBoundedConstructible B Y ⊓
    (fun K ↦ ∃ a b : ℤ, a ≤ b ∧
      Etale.DerivedCategory.hasTorAmplitudeIn B Y a b K)) (IB.obj MB)

/-- The four ordinary dualizing inputs are bounded constructible with finite Tor amplitude.

Source: lem-coef-finite-dualizing.proof.md, paragraph 3, and the expanded proof of
lem-coef-dualizing-closed-site, steps 1--3
(blueprint: lem-coef-closed-dualizing-etale-finiteness).

Proof: apply coefDualizingConstruction at P and Y and both positive coefficient
levels. Closed i is proper; identify identity-open compact support with closed
direct image. Composition of compact support identifies the Hom functors represented
by I_R omega_P and omega_Y. Bounded-below upper shriek puts the first representative
in D+, so coefDualizingConstruction_representing gives their counit-compatible
isomorphism. Transfer constructibility and Tor amplitude across it. The affine-space
Tate reduction affine_dualizing_coefficient identifies the scalar extension M_B
with omega_P,B. Its image under I_B followed by the preceding identification is
omega_Y,B. Transport finiteness again to obtain the last two clauses. The scalar
extension is the fixed adjunction left adjoint; uniqueness of left adjoints identifies
it with the ordinary scalarExtension used in the Tate reduction. This argument works
for the specified embedding and the empty source, and does not assume finite Tor
dimension of the quotient ring B as an A-module. -/
theorem closedDualizingEtaleFiniteness
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (r : ℕ)
    (Y : Scheme.{u}) [IsAffine Y]
    (i : Y ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of D.k))) [IsClosedImmersion i] :
    closedDualizingEtaleFinitenessProperty D l E m n hm hmn r Y i := by sorry

end AlgebraicGeometry.ProEtale
