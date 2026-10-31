/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.RationalSmoothPurityCanonical
public import WeilConjectures.AlgebraicGeometry.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPullbackExchange
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.SmoothPurityMap
public import WeilConjectures.SixFunctors.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteGeometricPurityMate
public import WeilConjectures.AlgebraicGeometry.RationalWeilPurityNaturalityMate
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
public import WeilConjectures.AlgebraicGeometry.IntegralPullbackComposition
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTateDatum
public import WeilConjectures.AlgebraicGeometry.PurityCompactSupportTransport
public import WeilConjectures.AlgebraicGeometry.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma
public import WeilConjectures.AlgebraicGeometry.IntegralAdjunctionBijection
public import WeilConjectures.SecSmoothPurity.RationalPurityTraceCoherence

/-!
# Geometric Frobenius equivariance of purity, counit and trace

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
thm-pur-weil-equivariance-of-purity-and-trace, coefficient-clause definitions
(blueprint: def-pur-weil-equivariance-data).
The coefficient clauses use the canonical maps, rather than hypothesized exchange laws.
Their published coordinate definitions are owned by def-pur-finite-geometric-comparison-data
and def-pur-field-geometric-comparison-data, re-exported without copying their declarations.

## Main definitions

* `exceptionalStructure` and `ThreeSquares` spell out the specified maps and equations.
* `FiniteClause`, `IntegralClause`, `RationalClause` and `CommonClause` instantiate them
  in the four coefficient categories.
* The `integral*` helpers restrict the published completed constructions to finite-Tor objects.

## Main statements

* The four coefficient clauses specify all three equations at their respective stages.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u uX uY vX vY

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityWeil

/-- The specified exceptional structure, in the order inverse purity, source comparison,
purity at PK, and G(phi). Source: blueprint definition of E_K and phi!
(blueprint: def-pur-weil-equivariance-data). -/
def exceptionalStructure {CX : Type uX} [Category.{vX} CX]
    (Q : CX ⥤ CX) {HK GK HPK GPK : CX}
    (gamma : HK ≅ GK) (gammaP : HPK ≅ GPK)
    (b : Q.obj HK ≅ HPK) (gphi : GPK ≅ GK) : Q.obj GK ≅ GK :=
  (Q.mapIso gamma).symm ≪≫ b ≪≫ gammaP ≪≫ gphi

/-- The three displayed squares. Here `b` is the independent pullback/tensor/Tate/shift
comparison, and `BH`, `BG` are the canonical compact-support exchanges. This helper only
abbreviates the three equations; the coefficient clauses below supply all its maps.
Source: blueprint, the three equations
(blueprint: def-pur-weil-equivariance-data). -/
def ThreeSquares {CX : Type uX} {CY : Type uY}
    [Category.{vX} CX] [Category.{vY} CY]
    (Q : CX ⥤ CX) (P : CY ⥤ CY) (F : CX ⥤ CY)
    {K : CY} {HK GK HPK GPK : CX}
    (phi : P.obj K ≅ K) (gamma : HK ≅ GK) (gammaP : HPK ≅ GPK)
    (b : Q.obj HK ≅ HPK) (hphi : HPK ≅ HK) (gphi : GPK ≅ GK)
    (epsilon : F.obj GK ⟶ K)
    (BH : P.obj (F.obj HK) ⟶ F.obj (Q.obj HK))
    (BG : P.obj (F.obj GK) ⟶ F.obj (Q.obj GK)) : Prop :=
  Q.map gamma.hom ≫ (exceptionalStructure Q gamma gammaP b gphi).hom =
      (b ≪≫ hphi).hom ≫ gamma.hom ∧
    P.map epsilon ≫ phi.hom =
      (BG ≫ F.map (exceptionalStructure Q gamma gammaP b gphi).hom) ≫ epsilon ∧
    P.map (F.map gamma.hom ≫ epsilon) ≫ phi.hom =
      (BH ≫ F.map (b ≪≫ hphi).hom) ≫ (F.map gamma.hom ≫ epsilon)

section Geometry

variable (P : PurityFiniteSetting.{u})
  (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

/-- The three squares at the positive finite level in P, in the fixed-scalar coordinates
of the existing intrinsic realization equivalence. Gamma includes both realization units.
Source: blueprint finite coefficient clause
(blueprint: def-pur-weil-equivariance-data). -/
def FiniteClause : Prop :=
  ∀ (K : DerivedCategory (Sheaf (ProEt.topology (P.frobeniusFiber Y₀).left)
      (ModuleCat.{u + 1} P.Coefficient)))
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos
      (P.frobeniusFiber Y₀).left
      ((sfIntrinsicDerivedEquivalence (P.frobeniusFiber Y₀).left P.Ring).functor.obj K))
    (phi : (P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj K ≅ K),
  ThreeSquares
    (P.smoothPurityPullback (P.frobeniusGaloisMap X₀))
    (P.smoothPurityPullback (P.frobeniusGaloisMap Y₀))
    (P.geometricPurityF (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom)
    phi
    (P.geometricPurityIso (P.frobeniusMap f₀) d K hK)
    (P.geometricPurityIso (P.frobeniusMap f₀) d
      ((P.smoothPurityPullback (P.frobeniusGaloisMap Y₀)).obj K)
      (P.geometricPurityInput Y₀ K hK))
    (P.geometricPuritySource X₀ Y₀ f₀ d K)
    ((P.smoothPurityPullback (P.frobeniusMap f₀) ⋙
      P.compositionTwistShift (P.frobeniusFiber X₀).left d).mapIso phi)
    ((P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
      (P.frobeniusFiber Y₀).hom).mapIso phi)
    (P.geometricPurityCounit (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom K)
    (P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
      (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
      (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
      ((P.smoothPurityPullback (P.frobeniusMap f₀) ⋙
        P.compositionTwistShift (P.frobeniusFiber X₀).left d).obj K))
    (P.geometricPurityB (P.frobeniusMap f₀) (P.frobeniusFiber Y₀).hom
      (P.frobeniusGaloisMap X₀) (P.frobeniusGaloisMap Y₀)
      (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1
      ((P.smoothPurityExceptionalOver (P.frobeniusMap f₀)
        (P.frobeniusFiber Y₀).hom).obj K))

variable (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := zlFiberMap P.field f₀))

/-- Rational squares, for every strict rational Weil structure, without requiring a
stable integral lattice. Source: blueprint rational coefficient clause
(blueprint: def-pur-weil-equivariance-data). -/
def RationalClause : Prop := by
  letI : SmoothOfRelativeDimension d (zlFiberMap P.field f₀) :=
    inferInstanceAs (SmoothOfRelativeDimension d (P.frobeniusMap f₀))
  exact
    ∀ (K : sfRationalConstructibleCategory P.coefficients.l P.extension
        (P.field.geometricFiber Y₀).left)
      (phi : (sfWeilFrobeniusPullback P.field P.coefficients.l
        P.coefficients.different Y₀ P.extension).obj K ≅ K),
    ThreeSquares
      (sfWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different X₀ P.extension)
      (sfWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different Y₀ P.extension)
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.rational ⟨P.extension⟩)).F
      phi (rationalWeilPurityGamma P f₀ c₀ S d K)
      (rationalWeilPurityGamma P f₀ c₀ S d
        ((sfWeilFrobeniusPullback P.field P.coefficients.l
          P.coefficients.different Y₀ P.extension).obj K))
      (RationalWeilPurity.b P.field P.coefficients.l P.coefficients.different f₀ P.extension d K)
      ((RationalWeilPurity.H P.field P.coefficients.l P.coefficients.different
        f₀ P.extension d).mapIso phi)
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.rational ⟨P.extension⟩)).G.mapIso phi)
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.rational ⟨P.extension⟩)).adjunction.counit.app K)
      ((RationalWeilPurity.beta P.field P.coefficients.l P.coefficients.different
        f₀ P.extension P.coefficients.Qbar c₀ S).hom.app
        ((RationalWeilPurity.H P.field P.coefficients.l P.coefficients.different
          f₀ P.extension d).obj K))
      ((RationalWeilPurity.beta P.field P.coefficients.l P.coefficients.different
        f₀ P.extension P.coefficients.Qbar c₀ S).hom.app
        ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
          (.rational ⟨P.extension⟩)).G.obj K))

/-- Common-stage squares on every object and every strict Weil isomorphism in the
actual common-stage category. Source: blueprint Qbar coefficient clause
(blueprint: def-pur-weil-equivariance-data). -/
def CommonClause : Prop := by
  letI : SmoothOfRelativeDimension d (zlFiberMap P.field f₀) :=
    inferInstanceAs (SmoothOfRelativeDimension d (P.frobeniusMap f₀))
  exact
    ∀ (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber Y₀).left)
      (phi : (sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l
        P.coefficients.different Y₀ P.coefficients.Qbar).obj K ≅ K),
    ThreeSquares
      (sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different
        X₀ P.coefficients.Qbar)
      (sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l P.coefficients.different
        Y₀ P.coefficients.Qbar)
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀) .closed).F
      phi (commonWeilPurityGamma P f₀ c₀ S d K)
      (commonWeilPurityGamma P f₀ c₀ S d
        ((sfCommonStageWeilFrobeniusPullback P.field P.coefficients.l
          P.coefficients.different Y₀ P.coefficients.Qbar).obj K))
      (CommonWeilPurity.b P.field P.coefficients.l P.coefficients.different
        f₀ P.coefficients.Qbar d K)
      ((CommonWeilPurity.H P.field P.coefficients.l P.coefficients.different
        f₀ P.coefficients.Qbar d).mapIso phi)
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀) .closed).G.mapIso phi)
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        .closed).adjunction.counit.app K)
      ((CommonWeilPurity.beta P.field P.coefficients.l P.coefficients.different
        f₀ P.coefficients.Qbar c₀ S).hom.app
        ((CommonWeilPurity.H P.field P.coefficients.l P.coefficients.different
          f₀ P.coefficients.Qbar d).obj K))
      ((CommonWeilPurity.beta P.field P.coefficients.l P.coefficients.different
        f₀ P.coefficients.Qbar c₀ S).hom.app
        ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀) .closed).G.obj K))

end Geometry

/-- Restrict the actual completed pullback to finite-Tor constructibles. Membership uses
residue-Tor equivalence, rather than an additional Tor hypothesis on its input.
Source: blueprint integral clause (blueprint: def-pur-weil-equivariance-data). -/
def integralPull (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)] :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X :=
  (finiteTorConstructibleIntegral P.coefficients.l P.extension X).lift
    ((finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι ⋙
      integralDerivedPullback P.coefficients.l P.extension f)
    (fun K ↦ (congrFun (integral_residue_tor P.field P.coefficients.l
      P.coefficients.different P.extension X).2 _).mp
        (((integralOperations_preserve_constructible P.coefficients.l P.extension f).1
          K.obj K.property.1).1))

section Source
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The actual completed twisted pullback as a functor on the finite-Tor category.
It has precisely the object formula of the published integral purity source.
Source: blueprint H (blueprint: def-pur-weil-equivariance-data). -/
def integralH :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X :=
  (finiteTorConstructibleIntegral P.coefficients.l P.extension X).lift
    (((Functor.const (finiteTorConstructibleIntegralCategory P.coefficients.l
      P.extension Y)).obj
      (RationalSmoothPurityCanonical.twist P X (X ↘ Spec (.of P.field.k)) d).obj).prod'
      ((finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι ⋙
        integralDerivedPullback P.coefficients.l P.extension f) ⋙
      integralCompletedTensor P.coefficients.l P.extension X)
    (RationalSmoothPurityCanonical.integralSource_mem P f d)

end Source

section Geometry
variable (P : PurityFiniteSetting.{u})
  (X₀ Y₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]

/-- Geometric Frobenius on the integral finite-Tor category, with the prime inverses
inherited from the finite-field datum. Source: blueprint P and Q
(blueprint: def-pur-weil-equivariance-data). -/
def integralP (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  @integralPull P _ _ (P.frobeniusGaloisMap T₀)
    (fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different T₀ x)
    (fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different T₀ x)

variable (d : ℕ) [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]

/-- The shifted integral root-line comparison uses the published completed-to-ordinary
comparison and the ordinary inverse-image shift constraint, followed by the canonical
root-tower Tate map. Source: blueprint tau_d and shift factor of b
(blueprint: def-pur-weil-equivariance-data). -/
def integralShiftedLine (T₀ : Over (Spec (.of P.field.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :
    (integralDerivedPullback P.coefficients.l P.extension (P.frobeniusGaloisMap T₀)).obj
      (RationalSmoothPurityCanonical.twist P (P.frobeniusFiber T₀).left
        (P.frobeniusFiber T₀).hom d).obj ≅
      (RationalSmoothPurityCanonical.twist P (P.frobeniusFiber T₀).left
        (P.frobeniusFiber T₀).hom d).obj := by
  letI : IsIso (P.frobeniusGaloisMap T₀) :=
    (P.field.geometricFrobenius T₀).isIso_hom
  letI : ∀ x : (P.frobeniusFiber T₀).left,
    Invertible (P.coefficients.l : (P.frobeniusFiber T₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different T₀ x
  exact (FrobeniusCoefficientTwists.completedToOrdinary P.coefficients.l P.extension
      (P.frobeniusGaloisMap T₀)).app
        ⟨_, (RationalSmoothPurityCanonical.twist P (P.frobeniusFiber T₀).left
          (P.frobeniusFiber T₀).hom d).property.1⟩ ≪≫
    (Functor.commShiftIso
      (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
        (P.frobeniusGaloisMap T₀)) (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (FrobeniusCoefficientTwists.ordinaryDerivedLineMap P.coefficients.l P.extension
        (P.frobeniusGaloisMap T₀) (d : ℤ))

/-- The independent integral b: completed tensor comparison, the shifted root line,
and pullback composition around the actual semilinear square. No purity map occurs.
Source: blueprint definition of b (blueprint: def-pur-weil-equivariance-data). -/
def integralB
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
      (P.frobeniusFiber Y₀).left) :
    (integralP P X₀).obj ((integralH P (P.frobeniusMap f₀) d).obj K) ≅
      (integralH P (P.frobeniusMap f₀) d).obj ((integralP P Y₀).obj K) := by
  letI : ∀ x : (P.frobeniusFiber X₀).left,
    Invertible (P.coefficients.l : (P.frobeniusFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x
  letI : ∀ y : (P.frobeniusFiber Y₀).left,
    Invertible (P.coefficients.l : (P.frobeniusFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different Y₀ y
  let cp : IntegralPullbackCompositionFamily P.coefficients.l P.extension :=
    (integralPullbackComposition P.coefficients.l P.extension).choose
  let K' : sfIntegralConstructibleCategory P.coefficients.l P.extension
      (P.frobeniusFiber Y₀).left := ⟨K.obj, K.property.1⟩
  let inc := (sfIntegralConstructible P.coefficients.l P.extension
    (P.frobeniusFiber X₀).left).ι
  let square :
      (integralDerivedPullback P.coefficients.l P.extension (P.frobeniusGaloisMap X₀)).obj
        ((integralDerivedPullback P.coefficients.l P.extension (P.frobeniusMap f₀)).obj
          K.obj) ≅
      (integralDerivedPullback P.coefficients.l P.extension (P.frobeniusMap f₀)).obj
        ((integralDerivedPullback P.coefficients.l P.extension (P.frobeniusGaloisMap Y₀)).obj
          K.obj) :=
    inc.mapIso ((@cp (P.frobeniusFiber Y₀).left (P.frobeniusFiber X₀).left
      (P.frobeniusFiber X₀).left inferInstance inferInstance inferInstance
      (P.frobeniusGaloisMap X₀) (P.frobeniusMap f₀)).app K').symm ≪≫
    eqToIso (congrArg (fun h ↦
      (integralDerivedPullback P.coefficients.l P.extension h).obj K.obj)
      (P.field.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1) ≪≫
    inc.mapIso ((@cp (P.frobeniusFiber Y₀).left (P.frobeniusFiber Y₀).left
      (P.frobeniusFiber X₀).left inferInstance inferInstance inferInstance
      (P.frobeniusMap f₀) (P.frobeniusGaloisMap Y₀)).app K')
  let line := RationalSmoothPurityCanonical.twist P (P.frobeniusFiber X₀).left
    (P.frobeniusFiber X₀).hom d
  let pullK := RationalSmoothPurityCanonical.pullFiniteTor P (P.frobeniusMap f₀) d K
  exact ObjectProperty.isoMk _
    (inc.mapIso (canonicalIntegralPullbackTensor P.coefficients.l P.extension
      (P.frobeniusGaloisMap X₀) ⟨line.obj, line.property.1⟩ ⟨_, pullK.1⟩) ≪≫
      (integralCompletedTensor P.coefficients.l P.extension
        (P.frobeniusFiber X₀).left).mapIso
          (Iso.prod (integralShiftedLine P d X₀) square))

variable (c₀ : Compactification f₀.left)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := zlFiberMap P.field f₀))

/-- Integral Gamma in the specified counit-preserving adjunction coordinates. The
published trace-transpose map is identified there with realized normalized tower purity.
Source: blueprint integral Gamma (blueprint: def-pur-weil-equivariance-data). -/
def integralGamma
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
      (P.frobeniusFiber Y₀).left) :=
  RationalSmoothPurityCanonical.integralIso P (P.frobeniusMap f₀)
    (zlGeometricCompactification P.field f₀ c₀) S d K

/-- The canonical completed proper/open exchange transported through the specified
integral left-functor comparison, and lifted through the full finite-Tor inclusion.
Source: blueprint B (blueprint: def-pur-weil-equivariance-data). -/
def integralBeta
    (M : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
      (P.frobeniusFiber X₀).left) :
    (integralP P Y₀).obj
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).F.obj M) ≅
      (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).F.obj ((integralP P X₀).obj M) := by
  letI : ∀ x : (P.frobeniusFiber X₀).left,
    Invertible (P.coefficients.l : (P.frobeniusFiber X₀).left.residueField x) :=
      fun x ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different X₀ x
  letI : ∀ y : (P.frobeniusFiber Y₀).left,
    Invertible (P.coefficients.l : (P.frobeniusFiber Y₀).left.residueField y) :=
      fun y ↦ sfWeilPrimeInvertible P.field P.coefficients.l P.coefficients.different Y₀ y
  let c := zlGeometricCompactification P.field f₀ c₀
  let e := S.ring.integralLeft c (AdicSmoothDualizing.fieldStage P)
  let inc := (sfIntegralConstructible P.coefficients.l P.extension
    (P.frobeniusFiber Y₀).left).ι
  exact ObjectProperty.isoMk (finiteTorConstructibleIntegral P.coefficients.l P.extension
    (P.frobeniusFiber Y₀).left)
    (inc.mapIso
      ((RationalWeilPurity.integralFrobenius P.field P.coefficients.l
        P.coefficients.different P.extension Y₀).mapIso (e.app M) ≪≫
      RationalWeilPurity.integralExchange P.field P.coefficients.l P.coefficients.different
        f₀ P.extension c₀
        ((PurCompactSupport.finiteTorIntegralInclusion P.coefficients.l P.extension
          (P.frobeniusFiber X₀).left).obj M) ≪≫
      (e.app ((integralP P X₀).obj M)).symm))

/-- The integral three squares in the derived-complete finite-Tor category. Every
comparison in this clause is the completed canonical map, not a family of its evaluations.
Source: blueprint integral clause
(blueprint: def-pur-weil-equivariance-data). -/
def IntegralClause : Prop :=
  ∀ (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension
      (P.frobeniusFiber Y₀).left)
    (phi : (integralP P Y₀).obj K ≅ K),
  ThreeSquares (integralP P X₀) (integralP P Y₀)
    (S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
      (.integral (AdicSmoothDualizing.fieldStage P))).F
    phi (integralGamma P X₀ Y₀ f₀ d c₀ S K)
    (integralGamma P X₀ Y₀ f₀ d c₀ S ((integralP P Y₀).obj K))
    (integralB P X₀ Y₀ f₀ d K)
    ((integralH P (P.frobeniusMap f₀) d).mapIso phi)
    ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
      (.integral (AdicSmoothDualizing.fieldStage P))).G.mapIso phi)
    ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
      (.integral (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app K)
    (integralBeta P X₀ Y₀ f₀ c₀ S ((integralH P (P.frobeniusMap f₀) d).obj K)).hom
    (integralBeta P X₀ Y₀ f₀ c₀ S
      ((S.ring.operation (zlGeometricCompactification P.field f₀ c₀)
        (.integral (AdicSmoothDualizing.fieldStage P))).G.obj K)).hom

end Geometry
end WeilConjectures.PurityWeil
