/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.CoefficientCohomologyModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ClosedPointField
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Local Frobenius on the derived point fibre and its alternating trace

Source: Weil blueprint, sec-poincare-duality/sk-lem-finite,
Local Frobenius and local alternating trace; Deligne, Weil II, (1.1.7)--(1.1.10)
(blueprint: def-weil-local-frobenius-trace).

The rational composition comparison below is the localization of the specified integral
comparison. Object equalities only identify the unchanged objects of raw rationalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identify the prescribed rational pullback object with its integral model.
Source: blueprint rational pullback convention (blueprint: def-weil-local-frobenius-trace). -/
def localPullbackObjectIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E f).obj K ≅
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K)

/-- The specified composition comparison, localized from the integral comparison.
Source: blueprint composition convention (blueprint: def-weil-local-frobenius-trace). -/
def localPullbackComposition {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfRationalConstructibleCategory l E Z) :
    (rationalDerivedPullback l E (h ≫ k)).obj K ≅
      (rationalDerivedPullback l E h).obj ((rationalDerivedPullback l E k).obj K) :=
  localPullbackObjectIso l E (h ≫ k) K ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (((integralPullbackComposition l E).choose h k).app K.obj) ≪≫
    (localPullbackObjectIso l E h
      ((sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralPullback l E k).obj K.obj))).symm ≪≫
    (rationalDerivedPullback l E h).mapIso (localPullbackObjectIso l E k K).symm

/-- Positive powers, with exponent n+1; this avoids any choice of a pullback unit.
Source: blueprint theta iteration (blueprint: def-weil-local-frobenius-trace). -/
def localPositivePower {X : Scheme.{u}} (g : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => g
  | n + 1 => localPositivePower g n ≫ g

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Derived pullback of the underlying Weil complex at an arbitrary geometric point.
Source: blueprint K_xbar (blueprint: def-weil-local-frobenius-trace). -/
def localDerivedStalk (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    sfRationalConstructibleCategory l E (Spec (.of D.k)) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (rationalDerivedPullback l E x).obj K.carrier

/-- The bounded finite-dimensional rational point complex C_xbar.
Source: blueprint point-fibre clause (blueprint: def-weil-local-frobenius-trace). -/
def localPointComplex (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    (DerivedCategory.pointFiniteDimensional E).FullSubcategory :=
  (pointRationalFibre D l hl E).obj (localDerivedStalk l E D hl Y₀ K x)

/-- The iterated Weil isomorphism theta^[n+1], with the specified comparison.
Source: blueprint theta^[1] and recurrence (blueprint: def-weil-local-frobenius-trace). -/
def localWeilIterate (K : sfWeilComplex D l hl Y₀ E) :
    (n : ℕ) →
    (@rationalDerivedPullback l _ E _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier ≅
      K.carrier
  | 0 => K.str
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    localPullbackComposition l E (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (D.geometricFrobenius Y₀).hom K.carrier ≪≫
      (rationalDerivedPullback l E
        (localPositivePower (D.geometricFrobenius Y₀).hom n)).mapIso K.str ≪≫
      localWeilIterate K n

/-- Point transport to the actual one-step rational pullback object.
Source: blueprint iota_N (blueprint: def-weil-local-frobenius-trace). -/
def localPointTransport (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (pointRationalFibre D l hl E).obj N ⟶
      (pointRationalFibre D l hl E).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _ (frobeniusPointIso D).hom
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N) :=
  frobeniusPointTransportRational D l hl E N ≫
    (pointRationalFibre D l hl E).map
      ((@localPullbackObjectIso l _ E _ _ _ _ _ (frobeniusPointIso D).hom
        (frobeniusPointPrimeInvertible D l hl)
        (frobeniusPointPrimeInvertible D l hl) N).inv)

/-- Compose iota_N, iota_GN, ... and then the inverse composition comparison.
The index n means exponent n+1.
Source: blueprint I^[n]_N (blueprint: def-weil-local-frobenius-trace). -/
def localPointTransportIterate (N : sfRationalConstructibleCategory l E (Spec (.of D.k))) :
    (n : ℕ) → (pointRationalFibre D l hl E).obj N ⟶
      (pointRationalFibre D l hl E).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)
  | 0 => localPointTransport l E D hl N
  | n + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    localPointTransport l E D hl N ≫
      localPointTransportIterate
        ((rationalDerivedPullback l E (frobeniusPointIso D).hom).obj N) n ≫
      (pointRationalFibre D l hl E).map
        (localPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointIso D).hom N).inv

/-- The middle comparison uses reparametrization of Spec(k), never a fixed scheme map.
Source: blueprint geometric-point return (blueprint: def-weil-local-frobenius-trace). -/
def localReturnComparison (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (localPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom n)
    x K.carrier).symm ≪≫
    eqToIso (congrArg (fun f ↦ (rationalDerivedPullback l E f).obj K.carrier) h.symm) ≪≫
    localPullbackComposition l E x
      (localPositivePower (D.geometricFrobenius Y₀).hom n) K.carrier

/-- The derived local operator: iterated point transport, return comparison,
then pullback of theta^[n+1]. Its index n denotes the positive exponent n+1.
Source: blueprint F_x^(n) (blueprint: def-weil-local-frobenius-trace). -/
def localFrobeniusOperator (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) :
    localPointComplex l E D hl Y₀ K x ⟶ localPointComplex l E D hl Y₀ K x :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  localPointTransportIterate l E D hl (localDerivedStalk l E D hl Y₀ K x) n ≫
    (pointRationalFibre D l hl E).map
      (localReturnComparison l E D hl Y₀ K x n h).hom ≫
    (pointRationalFibre D l hl E).map
      ((rationalDerivedPullback l E x).map (localWeilIterate l E D hl Y₀ K n).hom)

/-- The induced local operator on H^j(C_xbar), the coefficient stalk convention.
Source: blueprint cohomology clause (blueprint: def-weil-local-frobenius-trace). -/
def localFrobeniusCohomology (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) (j : ℤ) :=
  (DerivedCategory.coefficientFdCohomology E j).map
    (localFrobeniusOperator l E D hl Y₀ K x n h)

/-- The finite alternating sum, using the cohomological sign also in negative degrees.
Source: blueprint final display (blueprint: def-weil-local-frobenius-trace). -/
def localAlternatingTrace (K : sfWeilComplex D l hl Y₀ E)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) : E :=
  ∑ᶠ j : ℤ,
    (j.negOnePow : ℤ) • LinearMap.trace E
      ((DerivedCategory.coefficientFdCohomology E j).obj (localPointComplex l E D hl Y₀ K x))
      (localFrobeniusCohomology l E D hl Y₀ K x n h j).hom

/-- The finite-field inclusion and a point over k₀ have matching base maps.
Source: blueprint finite-field-point clause (blueprint: def-weil-local-frobenius-trace).
Proof: the composite of extensionEmbedding with the subfield inclusion is algebraMap.
Contravariant functoriality of Spec and the equation Over.w x give the equality. -/
theorem localExtensionPoint_compatible (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) :
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  sorry

/-- The geometric point obtained from F_(q^n) ⊂ k by the universal fibre-product lift.
Source: blueprint xbar (blueprint: def-weil-local-frobenius-trace). -/
def localExtensionPoint (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom (D.extensionSubfield n hn).subtype) ≫ x.left)
    (𝟙 _) (localExtensionPoint_compatible D Y₀ n hn x)

/-- The return is reparametrization, since geometric Frobenius to the n-th power
fixes the finite subfield pointwise.
Source: blueprint return equation (blueprint: def-weil-local-frobenius-trace).
Proof: lem-weil-unique-subfield-of-closure identifies the subfield with the roots of
X^(q^n)-X. Arithmetic Frobenius to the n-th power, and hence its inverse, fixes these
roots. Compare the two pullback projections: the model projection agrees by that
fixed-field equation; the closure projection is g_s^n on both sides. Pullback uniqueness
proves the displayed equation. Since hn makes n positive, (n-1)+1=n. -/
theorem localExtensionPoint_return (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) :
    localExtensionPoint D Y₀ n hn x ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
        localExtensionPoint D Y₀ n hn x := by
  sorry

/-- F_x^(n) for every positive finite-field extension point, with no return assumption.
Source: blueprint finite-field operator (blueprint: def-weil-local-frobenius-trace). -/
def localExtensionFrobenius (K : sfWeilComplex D l hl Y₀ E)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) :=
  localFrobeniusOperator l E D hl Y₀ K (localExtensionPoint D Y₀ n hn x) (n - 1)
    (localExtensionPoint_return D Y₀ n hn x)

/-- The alternating local trace at a positive finite-field extension point.
Source: blueprint Tr(F_x^(n)|K_xbar) (blueprint: def-weil-local-frobenius-trace). -/
def localExtensionTrace (K : sfWeilComplex D l hl Y₀ E)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) : E :=
  localAlternatingTrace l E D hl Y₀ K (localExtensionPoint D Y₀ n hn x) (n - 1)
    (localExtensionPoint_return D Y₀ n hn x)

/-- The degree of a closed point uses its actual residue field with its structure map.
Source: blueprint r=[κ(y):k₀] (blueprint: def-weil-local-frobenius-trace). -/
def localClosedPointDegree (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) : ℕ :=
  letI := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  Module.finrank D.k₀ (Y₀.left.residueField y.val)

/-- A closed point of a finite-type model has finite positive residue degree.
Source: blueprint closed-point clause; lem-kun-closed-point-field(a)
(blueprint: def-weil-local-frobenius-trace).
Proof: closedPoint_iff_residueField_trdeg_zero_and_finite gives finiteness over k₀.
A field is nonzero, so its finite vector-space dimension is positive. -/
theorem localClosedPointDegree_pos
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left}) :
    1 ≤ localClosedPointDegree D Y₀ y := by
  sorry

/-- A k₀-embedding of κ(y) gives a model point compatible with the base field.
Source: blueprint chosen residue-field embedding (blueprint: def-weil-local-frobenius-trace).
Proof: the structural composite of fromSpecResidueField is Spec of the residue-field
algebra map. Compose with Spec ι and use the displayed k₀-compatibility equation. -/
theorem localClosedPoint_compatible
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    (Spec.map (CommRingCat.ofHom ι) ≫ Y₀.left.fromSpecResidueField y.val) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  sorry

/-- The geometric point over a closed point for the chosen k₀-embedding of its residue field.
Source: blueprint ybar (blueprint: def-weil-local-frobenius-trace). -/
def localClosedPoint (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom ι) ≫ Y₀.left.fromSpecResidueField y.val) (𝟙 _)
    (localClosedPoint_compatible D Y₀ y ι hι)

/-- Geometric Frobenius to the residue degree returns the chosen closed-point lift.
Source: blueprint closed-point return (blueprint: def-weil-local-frobenius-trace).
Proof: the residue field is finite over k₀ by lem-kun-closed-point-field(a), with
q^r elements. Its embedded image is the unique subfield of that size by
lem-weil-unique-subfield-of-closure, hence is fixed by gamma^r. Compare both
projections of the pullback exactly as for localExtensionPoint_return. Positivity
of the degree identifies the positive-power index r-1 with exponent r. -/
theorem localClosedPoint_return
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    localClosedPoint D Y₀ y ι hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom
          (localClosedPointDegree D Y₀ y - 1) =
      localPositivePower (frobeniusPointIso D).hom (localClosedPointDegree D Y₀ y - 1) ≫
        localClosedPoint D Y₀ y ι hι := by
  sorry

/-- F_y on the derived point complex for a closed point and a chosen residue embedding.
Source: blueprint closed-point operator (blueprint: def-weil-local-frobenius-trace). -/
def localClosedFrobenius (K : sfWeilComplex D l hl Y₀ E)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :=
  localFrobeniusOperator l E D hl Y₀ K (localClosedPoint D Y₀ y ι hι)
    (localClosedPointDegree D Y₀ y - 1) (localClosedPoint_return D Y₀ y ι hι)

/-- The closed-point cohomological operator F_y in every integer degree.
Source: blueprint closed-point cohomology clause (blueprint: def-weil-local-frobenius-trace). -/
def localClosedFrobeniusCohomology (K : sfWeilComplex D l hl Y₀ E)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) (j : ℤ) :=
  localFrobeniusCohomology l E D hl Y₀ K (localClosedPoint D Y₀ y ι hι)
    (localClosedPointDegree D Y₀ y - 1) (localClosedPoint_return D Y₀ y ι hι) j

/-- The analogous alternating closed-point trace with the same cohomological signs.
Source: blueprint closed-point trace (blueprint: def-weil-local-frobenius-trace). -/
def localClosedTrace (K : sfWeilComplex D l hl Y₀ E)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) : E :=
  localAlternatingTrace l E D hl Y₀ K (localClosedPoint D Y₀ y ι hι)
    (localClosedPointDegree D Y₀ y - 1) (localClosedPoint_return D Y₀ y ι hι)

/-- The induced local operator in every cohomological degree at an extension point.
Source: blueprint H^j(C_xbar) (blueprint: def-weil-local-frobenius-trace). -/
def localExtensionFrobeniusCohomology (K : sfWeilComplex D l hl Y₀ E)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) (j : ℤ) :=
  localFrobeniusCohomology l E D hl Y₀ K (localExtensionPoint D Y₀ n hn x) (n - 1)
    (localExtensionPoint_return D Y₀ n hn x) j

/-- The local alternating trace for the complete finite-field and coefficient datum,
including the specified finite subextension E of the chosen algebraic closure Qbar.
Source: blueprint final display (blueprint: def-weil-local-frobenius-trace). -/
def localFrobeniusTrace (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : sfWeilComplex D c.l c.different Y₀ E.val)
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn) : E.val :=
  localExtensionTrace c.l E.val D c.different Y₀ K n hn x

/-- The closed-point trace with the same complete coefficient datum and a chosen
k₀-embedding of the actual residue field into k.
Source: blueprint analogous closed-point trace (blueprint: def-weil-local-frobenius-trace). -/
def localClosedPointTrace (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
    (E : Padic.FiniteCoefficientFields c.l c.Qbar)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (K : sfWeilComplex D c.l c.different Y₀ E.val)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) : E.val :=
  localClosedTrace c.l E.val D c.different Y₀ K y ι hι

end WeilConjectures

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The object identification with the literal finite stage, not an arbitrary iso.
Source: blueprint common-stage convention (blueprint: def-weil-local-frobenius-trace). -/
def localQbarPullbackStageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω f).obj K ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) f).obj K.obj) :=
  eqToIso ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 K)

/-- The composition comparison at algebraic coefficients is the published rational
comparison at the literal stage, with the specified object comparisons on its boundaries.
Source: blueprint composition convention (blueprint: def-weil-local-frobenius-trace). -/
def localQbarPullbackComposition {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonStageDerivedPullback l Ω (h ≫ k)).obj K ≅
      (commonStageDerivedPullback l Ω h).obj ((commonStageDerivedPullback l Ω k).obj K) :=
  localQbarPullbackStageIso l Ω (h ≫ k) K ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).mapIso
      (localPullbackComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) h k K.obj) ≪≫
    (localQbarPullbackStageIso l Ω h
      ((GeneralAlgebraicallyClosedCoefficients.inclusion K.stage).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω K.stage) k).obj K.obj))).symm ≪≫
    (commonStageDerivedPullback l Ω h).mapIso (localQbarPullbackStageIso l Ω k K).symm

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The same geometric stalk construction on a common-stage Weil pair.
Source: blueprint stalk convention (blueprint: def-weil-local-frobenius-trace). -/
def localQbarDerivedStalk (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (commonStageDerivedPullback l Ω x).obj K.carrier

/-- The algebraically closed bounded finite-dimensional point complex.
Source: blueprint C_xbar (blueprint: def-weil-local-frobenius-trace). -/
def localQbarPointComplex (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (pointQbarFibre D l hl Ω).obj (localQbarDerivedStalk l Ω D hl Y₀ K x)

/-- H^0 of the point complex, the linear stalk of a heart object.
Source: blueprint stalk cohomology convention (blueprint: def-weil-local-frobenius-trace). -/
def localQbarStalk (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) : ModuleCat.{u} Ω :=
  (DerivedCategory.coefficientQbarCohomology l Ω 0).obj
    (localQbarPointComplex l Ω D hl Y₀ K x)

/-- Iterate the actual common-stage Weil isomorphism using the same composition maps.
The index n means exponent n+1, as in localWeilIterate.
Source: blueprint theta iteration (blueprint: def-weil-local-frobenius-trace). -/
def localQbarWeilIterate (K : sfCommonStageWeilComplex D l hl Y₀ Ω) :
    (n : ℕ) →
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier ≅
        K.carrier
  | 0 => K.str
  | n + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    localQbarPullbackComposition l Ω
      (localPositivePower (D.geometricFrobenius Y₀).hom n)
      (D.geometricFrobenius Y₀).hom K.carrier ≪≫
        (commonStageDerivedPullback l Ω
          (localPositivePower (D.geometricFrobenius Y₀).hom n)).mapIso K.str ≪≫
        localQbarWeilIterate K n

/-- The actual point-fibre object comparison with its explicit stagewise formula.
Source: blueprint point-fibre convention (blueprint: def-weil-local-frobenius-trace). -/
def localQbarFibreObjIso
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (pointQbarFibre D l hl Ω).obj N ≅ pointQbarFibreObj D l hl Ω N :=
  eqToIso ((pointQbarFibre_existsUnique D l hl Ω).exists.choose_spec.1 N)

/-- Match the actual common-stage pullback object with its integral-object presentation.
Source: blueprint scalar-localization convention
(blueprint: def-weil-local-frobenius-trace). -/
def localQbarPointPullbackIso
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
      (frobeniusPointPrimeInvertible D l hl)
      (frobeniusPointPrimeInvertible D l hl)).obj N ≅
        frobeniusPointQbarPullbackObj D l hl Ω N :=
  @localQbarPullbackStageIso l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
    (frobeniusPointPrimeInvertible D l hl)
    (frobeniusPointPrimeInvertible D l hl) N ≪≫
      (GeneralAlgebraicallyClosedCoefficients.inclusion N.stage).mapIso
        (@localPullbackObjectIso l _
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω N.stage) _ _ _ _ _
          (frobeniusPointIso D).hom
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl) N.obj)

/-- The published restriction-and-coprojection point transport, with only prescribed
boundary object identifications. No invertibility is assumed or built into the definition.
Source: blueprint I_N (blueprint: def-weil-local-frobenius-trace). -/
def localQbarPointTransport
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (pointQbarFibre D l hl Ω).obj N ⟶
      (pointQbarFibre D l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _ (frobeniusPointIso D).hom
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N) :=
  (localQbarFibreObjIso l Ω D hl N).hom ≫ frobeniusPointTransportQbar D l hl Ω N ≫
    (localQbarFibreObjIso l Ω D hl (frobeniusPointQbarPullbackObj D l hl Ω N)).inv ≫
    (pointQbarFibre D l hl Ω).map (localQbarPointPullbackIso l Ω D hl N).inv

/-- Iterate point transport and the specified composition comparison; index n is n+1.
Source: blueprint I^[n] (blueprint: def-weil-local-frobenius-trace). -/
def localQbarPointTransportIterate
    (N : generalAlgebraicallyClosedConstructibleCategory l Ω (Spec (.of D.k))) :
    (n : ℕ) → (pointQbarFibre D l hl Ω).obj N ⟶
      (pointQbarFibre D l hl Ω).obj
        ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)
  | 0 => localQbarPointTransport l Ω D hl N
  | n + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    localQbarPointTransport l Ω D hl N ≫
      localQbarPointTransportIterate
        ((commonStageDerivedPullback l Ω (frobeniusPointIso D).hom).obj N) n ≫
      (pointQbarFibre D l hl Ω).map
        (localQbarPullbackComposition l Ω (localPositivePower (frobeniusPointIso D).hom n)
          (frobeniusPointIso D).hom N).inv

/-- The return comparison is induced by the semilinear scheme-map equality.
Source: blueprint geometric-point return (blueprint: def-weil-local-frobenius-trace). -/
def localQbarReturnComparison (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (localQbarPullbackComposition l Ω (localPositivePower (frobeniusPointIso D).hom n)
    x K.carrier).symm ≪≫
    eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj K.carrier) h.symm) ≪≫
    localQbarPullbackComposition l Ω x
      (localPositivePower (D.geometricFrobenius Y₀).hom n) K.carrier

/-- The closed-point Frobenius at algebraic coefficients: iterate restriction transport,
then the semilinear return comparison, then the actual Weil isomorphism. The point and
return theorem are exactly the finite-stage definitions already recorded by this node.
Source: blueprint closed-point F_y (blueprint: def-weil-local-frobenius-trace). -/
def localQbarClosedFrobenius (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    localQbarPointComplex l Ω D hl Y₀ K (localClosedPoint D Y₀ y ι hι) ⟶
      localQbarPointComplex l Ω D hl Y₀ K (localClosedPoint D Y₀ y ι hι) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  localQbarPointTransportIterate l Ω D hl
    (localQbarDerivedStalk l Ω D hl Y₀ K (localClosedPoint D Y₀ y ι hι))
      (localClosedPointDegree D Y₀ y - 1) ≫
    (pointQbarFibre D l hl Ω).map
      (localQbarReturnComparison l Ω D hl Y₀ K (localClosedPoint D Y₀ y ι hι)
        (localClosedPointDegree D Y₀ y - 1) (localClosedPoint_return D Y₀ y ι hι)).hom ≫
    (pointQbarFibre D l hl Ω).map
      ((commonStageDerivedPullback l Ω (localClosedPoint D Y₀ y ι hι)).map
        (localQbarWeilIterate l Ω D hl Y₀ K (localClosedPointDegree D Y₀ y - 1)).hom)

/-- The operator on H^0, hence the local geometric Frobenius on a sheaf stalk.
Source: blueprint F_y on cohomology (blueprint: def-weil-local-frobenius-trace). -/
def localQbarClosedFrobeniusStalk (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :=
  (DerivedCategory.coefficientQbarCohomology l Ω 0).map
    (localQbarClosedFrobenius l Ω D hl Y₀ K y ι hι)

/-- The H^0 stalk at the geometric point supplied by a chosen closed-point embedding.
Source: blueprint closed-point stalk (blueprint: def-weil-local-frobenius-trace). -/
def localQbarClosedStalk (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    ModuleCat.{u} Ω :=
  localQbarStalk l Ω D hl Y₀ K (localClosedPoint D Y₀ y ι hι)

end WeilConjectures
