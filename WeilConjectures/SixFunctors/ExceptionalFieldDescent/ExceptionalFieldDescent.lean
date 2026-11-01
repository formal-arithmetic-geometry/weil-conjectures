/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension

/-! # Localization and common-field descent of the integral exceptional adjunction

Source: Zheng, Propositions 2.23, 2.29, 3.16 and Section 5 (Lemma 5.22 and
Proposition 5.24); blueprint exceptional inverse-image coefficient construction
(blueprint: lem-sf-exceptional-field-descent).

The integral input is normalized through its prescribed compact-support identification.
It contains no rational or algebraically closed adjunction. Output functors are fixed on
all raw tensor morphisms and all common-field representatives. Scheme and algebraic-closure
universes are independent. All coefficient categories are the published categories.

## Main declarations

- `IntegralInput`: the integral adjunction and its prescribed scalar mates.
- `RationalOutput`: raw localized functors, adjunction and comparisons.
- `CommonStageData`, `CommonOutput`: represented common-field descent and its adjunction.
- `exists_field_descent`: existence of these outputs from the integral input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open TensorProduct
open WeilConjectures.ConstructibleExceptionalCoefficients (FieldStage)

namespace WeilConjectures.ExceptionalFieldDescent

variable (l : ℕ) [Fact l.Prime]

/-- The published integral scalar functor; zero is only its characteristic proof parameter.
Source: blueprint raw scalar-extension paragraph
(blueprint: lem-sf-exceptional-field-descent). -/
abbrev integralScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{u}) :=
  sfConstructibleIntegralScalarExtension 0 l (Fact.out : l.Prime).ne_zero
    E.carrier L.carrier i T

/-- The published raw rational scalar functor, with the identical proof parameter.
Source: blueprint raw scalar-extension paragraph
(blueprint: lem-sf-exceptional-field-descent). -/
abbrev rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
    (T : Scheme.{u}) :=
  sfRationalScalarExtension l E.carrier T 0 (Fact.out : l.Prime).ne_zero L.carrier i

/-- The published ordinary-to-completed normalization of the integral tensor shift.
Source: blueprint canonical scalar shifts (blueprint: lem-sf-exceptional-field-descent). -/
noncomputable instance integralScalarCommShift (E L : FieldStage.{u} l)
    (i : E.carrier →ₐ[Padic l] L.carrier) (T : Scheme.{u}) :
    (integralScalar l E L i T).CommShift ℤ :=
  (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique
    l E.carrier L.carrier i T).exists.choose

/-- The existing small model of a finite coefficient subfield of the chosen closure.
Source: blueprint common-field category (blueprint: lem-sf-exceptional-field-descent). -/
abbrev coefficientField (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    FieldStage.{u} l where
  carrier := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The prescribed normalized integral left functor, with its actual Roos action.
Source: blueprint integral-left realization (blueprint: lem-sf-exceptional-field-descent). -/
abbrev integralLeft (E : FieldStage.{u} l) :=
  sfCompactSupportFiniteIntegralFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    c E.carrier

/-- Its published raw rationalization, including the prescribed action on every tensor Hom.
Source: blueprint rational-left realization (blueprint: lem-sf-exceptional-field-descent). -/
abbrev rationalLeft (E : FieldStage.{u} l) :=
  sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
    c E.carrier

/-- Integral input after transport along its prescribed compact-support identification.
The residue-Tor equality in the conclusion identifies this domain with the finite-Tor
integral domain. The left scalar maps are the actual proper/open tensor-unit mates.
Only their left identity and composition equations are inputs; right coherence is not.
Source: blueprint exceptional construction, retained steps 17--19
(blueprint: lem-sf-exceptional-field-descent). -/
class IntegralInput where
  G (E : FieldStage.{u} l) :
    sfIntegralConstructibleCategory l E.carrier Y ⥤ sfIntegralConstructibleCategory l E.carrier X
  adjunction (E : FieldStage.{u} l) : integralLeft l D hl c E ⊣ G E
  [leftAdditive (E : FieldStage.{u} l) : (integralLeft l D hl c E).Additive]
  [rightAdditive (E : FieldStage.{u} l) : (G E).Additive]
  [leftLinear (E : FieldStage.{u} l) :
    (integralLeft l D hl c E).Linear (Padic.coefficientExtensionIntegers l E.carrier)]
  [rightLinear (E : FieldStage.{u} l) :
    (G E).Linear (Padic.coefficientExtensionIntegers l E.carrier)]
  [leftShift (E : FieldStage.{u} l) : (integralLeft l D hl c E).CommShift ℤ]
  [rightShift (E : FieldStage.{u} l) : (G E).CommShift ℤ]
  leftExact (E : FieldStage.{u} l) : (integralLeft l D hl c E).IsTriangulated
  rightExact (E : FieldStage.{u} l) : (G E).IsTriangulated
  unitShift (E : FieldStage.{u} l) : (adjunction E).unit.CommShift ℤ
  counitShift (E : FieldStage.{u} l) : (adjunction E).counit.CommShift ℤ
  q (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    integralLeft l D hl c E ⋙ integralScalar l E L i Y ≅
      integralScalar l E L i X ⋙ integralLeft l D hl c L
  qCanonical (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    SfCompactSupportIntegralBetaSpec l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
      c E.carrier L.carrier i (q E L i)
  b (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    G E ⋙ integralScalar l E L i X ≅ integralScalar l E L i Y ⋙ G L
  counit (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (M : sfIntegralConstructibleCategory l E.carrier Y) :
    (q E L i).hom.app ((G E).obj M) ≫
      (integralLeft l D hl c L).map ((b E L i).hom.app M) ≫
        (adjunction L).counit.app ((integralScalar l E L i Y).obj M) =
      (integralScalar l E L i Y).map ((adjunction E).counit.app M)
  qShift (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (q E L i).hom.CommShift ℤ
  bShift (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (b E L i).hom.CommShift ℤ
  identity (E : FieldStage.{u} l) (K : sfIntegralConstructibleCategory l E.carrier X) :
    (q E E (AlgHom.id (Padic l) E.carrier)).hom.app K ≫
      (integralLeft l D hl c E).map
        ((sfIntegralScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfIntegralScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((integralLeft l D hl c E).obj K)
  composition (E L M : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (j : L.carrier →ₐ[Padic l] M.carrier)
      (K : sfIntegralConstructibleCategory l E.carrier X) :
    (integralScalar l L M j Y).map ((q E L i).hom.app K) ≫
      (q L M j).hom.app ((integralScalar l E L i X).obj K) ≫
      (integralLeft l D hl c M).map
        ((sfIntegralScalarComp l E.carrier L.carrier i X 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app K) =
      (sfIntegralScalarComp l E.carrier L.carrier i Y 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
            ((integralLeft l D hl c E).obj K) ≫ (q E M (j.comp i)).hom.app K

attribute [instance_reducible] IntegralInput.leftShift IntegralInput.rightShift

attribute [instance] IntegralInput.leftAdditive IntegralInput.rightAdditive
  IntegralInput.leftLinear IntegralInput.rightLinear IntegralInput.leftShift
  IntegralInput.rightShift

/-- Rational output, with no rational adjunction assumed in the integral input.
All tensor formulas quantify over arbitrary localized scalars, hence also every fraction.
Source: blueprint exceptional construction, retained steps 17--18
(blueprint: lem-sf-exceptional-field-descent). -/
class RationalOutput [I : IntegralInput l D hl c] where
  G (E : FieldStage.{u} l) :
    sfRationalConstructibleCategory l E.carrier Y ⥤ sfRationalConstructibleCategory l E.carrier X
  adjunction (E : FieldStage.{u} l) : rationalLeft l D hl c E ⊣ G E
  [leftAdditive (E : FieldStage.{u} l) : (rationalLeft l D hl c E).Additive]
  [rightAdditive (E : FieldStage.{u} l) : (G E).Additive]
  [leftShift (E : FieldStage.{u} l) : (rationalLeft l D hl c E).CommShift ℤ]
  [rightShift (E : FieldStage.{u} l) : (G E).CommShift ℤ]
  [scalarShiftX (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (rationalScalar l E L i X).CommShift ℤ]
  [scalarShiftY (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (rationalScalar l E L i Y).CommShift ℤ]
  scalarShiftXLocalized (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : sfIntegralConstructibleCategory l E.carrier X) :
    HEq (((rationalScalar l E L i X).commShiftIso (1 : ℤ)).hom.app
      ((sfRationalConstructibleLocalization l E.carrier X).obj K))
      ((sfRationalConstructibleLocalization l L.carrier X).map
        (((integralScalar l E L i X).commShiftIso (1 : ℤ)).hom.app K))
  scalarShiftYLocalized (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (M : sfIntegralConstructibleCategory l E.carrier Y) :
    HEq (((rationalScalar l E L i Y).commShiftIso (1 : ℤ)).hom.app
      ((sfRationalConstructibleLocalization l E.carrier Y).obj M))
      ((sfRationalConstructibleLocalization l L.carrier Y).map
        (((integralScalar l E L i Y).commShiftIso (1 : ℤ)).hom.app M))
  leftExact (E : FieldStage.{u} l) : (rationalLeft l D hl c E).IsTriangulated
  rightExact (E : FieldStage.{u} l) : (G E).IsTriangulated
  unitShift (E : FieldStage.{u} l) : (adjunction E).unit.CommShift ℤ
  counitShift (E : FieldStage.{u} l) : (adjunction E).counit.CommShift ℤ
  rightObjects (E : FieldStage.{u} l) (M : sfIntegralConstructibleCategory l E.carrier Y) :
    (G E).obj ((sfRationalConstructibleLocalization l E.carrier Y).obj M) =
      (sfRationalConstructibleLocalization l E.carrier X).obj ((I.G E).obj M)
  rightTensors (E : FieldStage.{u} l)
      (M N : sfIntegralConstructibleCategory l E.carrier Y) (h : M ⟶ N)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) :
    HEq ((G E).map (a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier] h))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier] (I.G E).map h :
        (sfRationalConstructibleLocalization l E.carrier X).obj ((I.G E).obj M) ⟶
          (sfRationalConstructibleLocalization l E.carrier X).obj ((I.G E).obj N))
  unit (E : FieldStage.{u} l) (K : sfIntegralConstructibleCategory l E.carrier X) :
    HEq ((adjunction E).unit.app ((sfRationalConstructibleLocalization l E.carrier X).obj K))
      ((sfRationalConstructibleLocalization l E.carrier X).map ((I.adjunction E).unit.app K))
  counit (E : FieldStage.{u} l) (M : sfIntegralConstructibleCategory l E.carrier Y) :
    HEq ((adjunction E).counit.app ((sfRationalConstructibleLocalization l E.carrier Y).obj M))
      ((sfRationalConstructibleLocalization l E.carrier Y).map ((I.adjunction E).counit.app M))
  hom (E : FieldStage.{u} l) (K : sfIntegralConstructibleCategory l E.carrier X)
      (M : sfIntegralConstructibleCategory l E.carrier Y)
      (h : (integralLeft l D hl c E).obj K ⟶ M)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) :
    HEq ((adjunction E).homEquiv
      ((sfRationalConstructibleLocalization l E.carrier X).obj K)
      ((sfRationalConstructibleLocalization l E.carrier Y).obj M)
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier] h))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier] (I.adjunction E).homEquiv K M h :
        (sfRationalConstructibleLocalization l E.carrier X).obj K ⟶
          (sfRationalConstructibleLocalization l E.carrier X).obj ((I.G E).obj M))
  homInverse (E : FieldStage.{u} l) (K : sfIntegralConstructibleCategory l E.carrier X)
      (M : sfIntegralConstructibleCategory l E.carrier Y) (h : K ⟶ (I.G E).obj M)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l E.carrier)) :
    HEq (((adjunction E).homEquiv
      ((sfRationalConstructibleLocalization l E.carrier X).obj K)
      ((sfRationalConstructibleLocalization l E.carrier Y).obj M)).symm
        ((a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier] h) ≫
          eqToHom (rightObjects E M).symm))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E.carrier]
        ((I.adjunction E).homEquiv K M).symm h :
        (sfRationalConstructibleLocalization l E.carrier Y).obj
          ((integralLeft l D hl c E).obj K) ⟶
            (sfRationalConstructibleLocalization l E.carrier Y).obj M)
  localizationLeft (E : FieldStage.{u} l) :
    integralLeft l D hl c E ⋙ sfRationalConstructibleLocalization l E.carrier Y ≅
      sfRationalConstructibleLocalization l E.carrier X ⋙ rationalLeft l D hl c E
  localizationRight (E : FieldStage.{u} l) :
    I.G E ⋙ sfRationalConstructibleLocalization l E.carrier X ≅
      sfRationalConstructibleLocalization l E.carrier Y ⋙ G E
  localizationLeftIdentity (E : FieldStage.{u} l)
      (K : sfIntegralConstructibleCategory l E.carrier X) :
    HEq ((localizationLeft E).hom.app K)
      (𝟙 ((sfRationalConstructibleLocalization l E.carrier Y).obj
        ((integralLeft l D hl c E).obj K)))
  localizationRightIdentity (E : FieldStage.{u} l)
      (M : sfIntegralConstructibleCategory l E.carrier Y) :
    HEq ((localizationRight E).hom.app M)
      (𝟙 ((sfRationalConstructibleLocalization l E.carrier X).obj ((I.G E).obj M)))
  localizationLeftShift (E : FieldStage.{u} l) :
    (localizationLeft E).hom.CommShift ℤ
  localizationRightShift (E : FieldStage.{u} l) :
    (localizationRight E).hom.CommShift ℤ
  localizationCounit (E : FieldStage.{u} l)
      (M : sfIntegralConstructibleCategory l E.carrier Y) :
    (localizationLeft E).hom.app ((I.G E).obj M) ≫
      (rationalLeft l D hl c E).map ((localizationRight E).hom.app M) ≫
        (adjunction E).counit.app ((sfRationalConstructibleLocalization l E.carrier Y).obj M) =
      (sfRationalConstructibleLocalization l E.carrier Y).map ((I.adjunction E).counit.app M)
  q (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    rationalLeft l D hl c E ⋙ rationalScalar l E L i Y ≅
      rationalScalar l E L i X ⋙ rationalLeft l D hl c L
  b (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    G E ⋙ rationalScalar l E L i X ≅ rationalScalar l E L i Y ⋙ G L
  qLocalized (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : sfIntegralConstructibleCategory l E.carrier X) :
    HEq ((q E L i).hom.app ((sfRationalConstructibleLocalization l E.carrier X).obj K))
      ((sfRationalConstructibleLocalization l L.carrier Y).map ((I.q E L i).hom.app K))
  bLocalized (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (M : sfIntegralConstructibleCategory l E.carrier Y) :
    HEq ((b E L i).hom.app ((sfRationalConstructibleLocalization l E.carrier Y).obj M))
      ((sfRationalConstructibleLocalization l L.carrier X).map ((I.b E L i).hom.app M))
  counitSquare (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (M : sfRationalConstructibleCategory l E.carrier Y) :
    (q E L i).hom.app ((G E).obj M) ≫
      (rationalLeft l D hl c L).map ((b E L i).hom.app M) ≫
        (adjunction L).counit.app ((rationalScalar l E L i Y).obj M) =
      (rationalScalar l E L i Y).map ((adjunction E).counit.app M)
  qShift (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (q E L i).hom.CommShift ℤ
  bShift (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier) :
    (b E L i).hom.CommShift ℤ
  identityLeft (E : FieldStage.{u} l) (K : sfRationalConstructibleCategory l E.carrier X) :
    (q E E (AlgHom.id (Padic l) E.carrier)).hom.app K ≫
      (rationalLeft l D hl c E).map
        ((sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app K) =
      (sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app
        ((rationalLeft l D hl c E).obj K)
  identityRight (E : FieldStage.{u} l) (M : sfRationalConstructibleCategory l E.carrier Y) :
    (b E E (AlgHom.id (Padic l) E.carrier)).hom.app M ≫
      (G E).map
        ((sfRationalScalarUnit l E.carrier Y 0 (Fact.out : l.Prime).ne_zero).hom.app M) =
      (sfRationalScalarUnit l E.carrier X 0 (Fact.out : l.Prime).ne_zero).hom.app ((G E).obj M)
  compositionLeft (E L M : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (j : L.carrier →ₐ[Padic l] M.carrier)
      (K : sfRationalConstructibleCategory l E.carrier X) :
    (rationalScalar l L M j Y).map ((q E L i).hom.app K) ≫
      (q L M j).hom.app ((rationalScalar l E L i X).obj K) ≫
      (rationalLeft l D hl c M).map
        ((sfRationalScalarComp l E.carrier L.carrier i X 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app K) =
      (sfRationalScalarComp l E.carrier L.carrier i Y 0
          (Fact.out : l.Prime).ne_zero M.carrier j).hom.app
            ((rationalLeft l D hl c E).obj K) ≫ (q E M (j.comp i)).hom.app K
  compositionRight (E L M : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (j : L.carrier →ₐ[Padic l] M.carrier)
      (N : sfRationalConstructibleCategory l E.carrier Y) :
    (rationalScalar l L M j X).map ((b E L i).hom.app N) ≫
      (b L M j).hom.app ((rationalScalar l E L i Y).obj N) ≫
      (G M).map ((sfRationalScalarComp l E.carrier L.carrier i Y 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app N) =
      (sfRationalScalarComp l E.carrier L.carrier i X 0
        (Fact.out : l.Prime).ne_zero M.carrier j).hom.app ((G E).obj N) ≫
          (b E M (j.comp i)).hom.app N

attribute [instance_reducible] RationalOutput.leftShift RationalOutput.rightShift
  RationalOutput.scalarShiftX RationalOutput.scalarShiftY
attribute [instance] RationalOutput.leftAdditive RationalOutput.rightAdditive
  RationalOutput.leftShift RationalOutput.rightShift
  RationalOutput.scalarShiftX RationalOutput.scalarShiftY

/-- The specified quotient functors on pairs and their common-stage adjunction.
The `Morphism.functor` definition acts on a representative by `beta; F(h); beta inverse`;
thus the two stage systems fix the action on every Hom colimit, including different fields.
The stage equations pin their comparisons to the rational images of the integral mates.
Source: blueprint exceptional construction, retained step 19
(blueprint: lem-sf-exceptional-field-descent). -/
structure CommonStageData (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [I : IntegralInput l D hl c]
    [R : RationalOutput l D hl c] where
  leftSystem : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y)
  rightSystem : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).Morphism
    (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X)
  leftStages (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    HEq (leftSystem.Φ E) (rationalLeft l D hl c (coefficientField l Ω E))
  rightStages (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    HEq (rightSystem.Φ E) (R.G (coefficientField l Ω E))
  leftComparisons (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    HEq (leftSystem.β h)
      (R.q (coefficientField l Ω E) (coefficientField l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h))
  rightComparisons (E L : AlgebraicallyClosedCoefficients.Index l Ω) (h : E ≤ L) :
    HEq (rightSystem.β h)
      (R.b (coefficientField l Ω E) (coefficientField l Ω L)
        (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h))
  stageAdjunction (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    leftSystem.Φ E ⊣ rightSystem.Φ E
  stageAdjunction_eq (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    HEq (stageAdjunction E) (R.adjunction (coefficientField l Ω E))
  [leftStageShift (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (leftSystem.Φ E).CommShift ℤ]
  [rightStageShift (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (rightSystem.Φ E).CommShift ℤ]
  leftStageShift_eq (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    HEq (leftStageShift E) (R.leftShift (coefficientField l Ω E))
  rightStageShift_eq (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    HEq (rightStageShift E) (R.rightShift (coefficientField l Ω E))

/-- Adjunction and normalized comparisons on the specified common-stage functors.
Source: blueprint retained step 19 (blueprint: lem-sf-exceptional-field-descent). -/
structure CommonOutput (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] [I : IntegralInput l D hl c]
    [R : RationalOutput l D hl c] (S : CommonStageData l D hl c Ω (R := R)) where
  adjunction : S.leftSystem.functor ⊣ S.rightSystem.functor
  [leftAdditive : S.leftSystem.functor.Additive]
  [rightAdditive : S.rightSystem.functor.Additive]
  [leftShift : S.leftSystem.functor.CommShift ℤ]
  [rightShift : S.rightSystem.functor.CommShift ℤ]
  leftExact : S.leftSystem.functor.IsTriangulated
  rightExact : S.rightSystem.functor.IsTriangulated
  unitShift : adjunction.unit.CommShift ℤ
  counitShift : adjunction.counit.CommShift ℤ
  q (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    S.leftSystem.Φ E ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E ≅
      GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E ⋙
        S.leftSystem.functor
  b (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    S.rightSystem.Φ E ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E ≅
      GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E ⋙
        S.rightSystem.functor
  qIdentity (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    HEq ((q E).hom.app K)
      (𝟙 ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E).obj
        ((S.leftSystem.Φ E).obj K)))
  bIdentity (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    HEq ((b E).hom.app M)
      (𝟙 ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj
        ((S.rightSystem.Φ E).obj M)))
  qShift (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (fun [_inclusionShiftX : (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := X) E).CommShift ℤ]
      [_inclusionShiftY : (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Y) E).CommShift ℤ]
      [_stageShift : (S.leftSystem.Φ E).CommShift ℤ]
      [_outerShift : S.leftSystem.functor.CommShift ℤ] ↦ (q E).hom.CommShift ℤ)
        (_inclusionShiftX := GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
        (_inclusionShiftY := GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
        (_stageShift := S.leftStageShift E) (_outerShift := leftShift)
  bShift (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (fun [_inclusionShiftX : (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := X) E).CommShift ℤ]
      [_inclusionShiftY : (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Y) E).CommShift ℤ]
      [_stageShift : (S.rightSystem.Φ E).CommShift ℤ]
      [_outerShift : S.rightSystem.functor.CommShift ℤ] ↦ (b E).hom.CommShift ℤ)
        (_inclusionShiftX := GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
        (_inclusionShiftY := GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
        (_stageShift := S.rightStageShift E) (_outerShift := rightShift)
  counitSquare (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E) :
    (q E).hom.app ((S.rightSystem.Φ E).obj M) ≫
      S.leftSystem.functor.map ((b E).hom.app M) ≫ adjunction.counit.app
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E).map
        ((S.stageAdjunction E).counit.app M)
  unit (K : GeneralAlgebraicallyClosedCoefficients.Pair l Ω X) :
    HEq (adjunction.unit.app K)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X)
        K.stage).map ((S.stageAdjunction K.stage).unit.app K.obj))
  counit (M : GeneralAlgebraicallyClosedCoefficients.Pair l Ω Y) :
    HEq (adjunction.counit.app M)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y)
        M.stage).map ((S.stageAdjunction M.stage).counit.app M.obj))
  hom (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
      (M : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E)
      (h : (S.leftSystem.Φ E).obj K ⟶ M) :
    adjunction.homEquiv
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj K)
        ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E).obj M)
        ((q E).inv.app K ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Y) E).map h) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).map
        ((S.stageAdjunction E).homEquiv K M h) ≫ (b E).hom.app M

end Geometry
end WeilConjectures.ExceptionalFieldDescent
