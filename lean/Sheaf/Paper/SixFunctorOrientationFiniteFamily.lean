/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module
public import Sheaf.Paper.SixFunctorOrientationDatum
public import Sheaf.Paper.OrientationFiniteCoefficientTwists

/-! # Finite components and their canonical realization
Source: def-sf-orientation, clauses 3 and 4 (blueprint: def-sf-orientation-finite-realization). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Invertibility supplied by the fixed coefficient convention on every space.
Source: ell distinct from p (blueprint: def-sf-orientation-finite-realization).
Proof: ell is a unit in the base field. Map it through GammaSpecIso and the
structure homomorphism on global sections. These maps preserve units even on
an empty scheme; no separatedness of the base is used. -/
theorem sfOrientationPrimeUnit (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : SixFunctorSpace D) : IsUnit (C.l : Γ(X.obj.left, ⊤)) := by
  sorry

/-- The coefficient line at a positive finite level, in the existing bounded
constructible category. It is the actual derived reduction of the completed line.
Source: finite reductions (blueprint: def-sf-orientation-finite-realization). -/
def sfOrientationReducedLine (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m : ℕ) (X : SixFunctorSpace D) (d : ℕ) :=
  (sixFunctorIntegralReduction D C E m X).obj (sfOrientationIntegralLineOn D C E X d)

/-- The degree-zero shifted etale root line is the derived coefficient unit.
Source: unit convention in clause 3 (blueprint: def-sf-orientation-finite-realization). -/
def sfOrientationEtaleLineZero (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (X : Scheme.{u}) :
    sfOrientationEtaleLine A N hA X 0 ≅ 𝟙_ (Etale.DerivedCategoryModule A X) :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X

/-- The finite comparison at the coefficient unit, obtained from the same root
comparison as every positive power. Source: clause 3
(blueprint: def-sf-orientation-finite-realization). -/
def sfOrientationFiniteSiteUnit (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (m r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (X : SixFunctorSpace D) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient C.l E m))
    X.obj.left).mapDerivedCategory.mapIso
      (sfOrientationEtaleLineZero (finiteTateCoefficient C.l E m)
        (C.l ^ (r + 1)) hA X.obj.left).symm ≪≫
    sfOrientationFiniteSiteLine C.l E X.obj.left (sfOrientationPrimeUnit D C X) m r hA 0

/-- The realization arrow on the dualizing object is induced by the actual unit
of nu* dashv Rnu*, followed by the specified intrinsic realization and the finite
exceptional comparison. No freely chosen exceptional comparison occurs here.
Source: the explicit w_C formula in clause 3 (blueprint: def-sf-orientation-finite-realization). -/
def sfOrientationFiniteOmegaRealization
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    {m : ℕ} (S : SixFunctorFiniteOperations D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [HasCompactification f.hom.left]
    (c : Compactification f.hom.left) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient C.l E m))
      X.obj.left).mapDerivedCategory.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} (finiteTateCoefficient C.l E m))
          f.hom.left) ⟶
    (sfIntrinsicDerivedEquivalence X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))).inverse.obj
        ((S.finite.exceptional f c).obj (sfOrientationReducedLine D C E m Y 0)).obj :=
  letI := c.hasCompactification
  let A := finiteTateCoefficient C.l E m
  let V := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory
  let F := Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f.hom.left
  let R := (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y.obj.left).rightDerivedFunctor
  let Q := sfIntrinsicDerivedEquivalence X.obj.left
    (Padic.coefficientExtensionRing C.l E (m + 1))
  V.map (F.map
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y.obj.left).unit.app
      (𝟙_ (Etale.DerivedCategoryModule A Y.obj.left)))) ≫
    V.map (F.map (R.map (sfOrientationFiniteSiteUnit D C E m r hA Y).hom)) ≫
    Q.unitIso.hom.app _ ≫
    Q.inverse.map ((S.finiteExceptional f c).inv.app
      (sfOrientationReducedLine D C E m Y 0))

/-- Left side of the finite realization equation, with the compactification
instance supplied by its coordinate. Source: clause 3
(blueprint: def-sf-orientation-finite-realization). -/
def sfOrientationFiniteRealizationLeft
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (S : SixFunctorFiniteOperations D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    (O : SfFiniteEtaleOrientation D (finiteTateCoefficient C.l E m) (C.l ^ (r + 1))
      (pow_pos (Fact.out : C.l.Prime).pos _) hA
      (fun X ↦ by simpa only [Nat.cast_pow] using (sfOrientationPrimeUnit D C X).pow (r + 1)))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsSeparated f.hom.left]
    (d : ℕ) [SmoothOfRelativeDimension d f.hom.left] (c : Compactification f.hom.left) :=
  letI := c.hasCompactification
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (finiteTateCoefficient C.l E m))
    X.obj.left).mapDerivedCategory.map (O.component f d).hom ≫
      sfOrientationFiniteOmegaRealization S r hA f c

/-- Right side of the same realization equation, using the canonical line
comparison and the actual intrinsic equivalence. Source: clause 3
(blueprint: def-sf-orientation-finite-realization). -/
def sfOrientationFiniteRealizationRight
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (S : SixFunctorFiniteOperations D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)))
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) (d : ℕ) (c : Compactification f.hom.left)
    (gamma : sfOrientationReducedLine D C E m X d ≅
      (S.finite.exceptional f c).obj (sfOrientationReducedLine D C E m Y 0)) :=
  letI := dlAdicGeometricResidueInvertible D C X.obj.left
  (sfOrientationFiniteSiteLine C.l E X.obj.left (sfOrientationPrimeUnit D C X)
    m r hA d).hom ≫
    (sfIntrinsicDerivedEquivalence X.obj.left
      (Padic.coefficientExtensionRing C.l E (m + 1))).inverse.map gamma.hom.hom

/-- Finite pro-etale components, all ordinary-etale companions, and their
realization equation. Geometry and affine normalization are checked in the
fully faithful ordinary-etale realization; the comparison is the actual unit
arrow above. This is an equivalent coordinate presentation, not extra purity data.
Source: finite part and realization of def-sf-orientation
(blueprint: def-sf-orientation-finite-realization). -/
structure SfFiniteOrientation {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (S : SixFunctorFiniteOperations D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m))) where
  component : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    sfOrientationReducedLine D C E m X d ≅
      (S.finite.exceptional f c).obj (sfOrientationReducedLine D C E m Y 0)
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c c' : Compactification f.hom.left),
    component f d c ≪≫ (S.finite.exceptionalComparison f c c').app
      (sfOrientationReducedLine D C E m Y 0) = component f d c'
  etale : ∀ (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0),
    SfFiniteEtaleOrientation D (finiteTateCoefficient C.l E m) (C.l ^ (r + 1))
      (pow_pos (Fact.out : C.l.Prime).pos _) hA
      (fun X ↦ by simpa only [Nat.cast_pow] using (sfOrientationPrimeUnit D C X).pow (r + 1))
  realization : ∀ (r : ℕ)
    (hA : ((C.l ^ (r + 1) : ℕ) : finiteTateCoefficient C.l E m) = 0)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    HEq (sfOrientationFiniteRealizationLeft S r hA (etale r hA) f d c)
      (sfOrientationFiniteRealizationRight S r hA f d c (component f d c))

/-- The A5 orientation equation for reduction from the completed coefficient stage.
The finite root line has deliberately been presented as that actual reduction.
Source: clause 3 (blueprint: def-sf-orientation-finite-realization). -/
def SfIntegralFiniteOrientationCompatible
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    {H : SixFunctorHigherOperations D C E}
    (I : SixFunctorIntegralNormalization D C E H) (O : SfHigherOrientation H)
    (m : ℕ) (F : SfFiniteOrientation (I.finiteLevels m)) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    (sixFunctorIntegralReduction D C E m X).map (O.integral.component f d c).hom ≫
      ((I.reduction m).supportAdjunction f c).right.hom.app
        (sfOrientationIntegralLineOn D C E Y 0) = (F.component f d c).hom

end WeilConjectures
