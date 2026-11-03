/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralCoefficientComparison.IntegralAdjointFiniteFreeCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTotalComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.TowerDiagonalFiniteEvaluation.TowerDiagonalFiniteEvaluation
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-! # Data for general-field integral diagonal comparison

(blueprint: def-pur-general-integral-diagonal-comparison-data).

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-integral-adjunction/
sk-prop-sp-integral-adjunction-bijection.proof.md, Purity paragraph; and
literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-purity-transport/
sk-thm-purity-transport.proof.md, Steps 1, 2 and 4 (coefficient change).
(blueprint: lem-pur-general-integral-diagonal-comparison).

The integral category is the ordinary native module derived category over coefficientRing.
All tower maps are maps in a derived category of strict varying-coefficient systems.
The given Edge fixes compact support, its tower adjoint, its counit, reduction and limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.GeneralIntegralDiagonalComparison
open IntegralDirectImageTower CurrentNativeIntegralTower IntegralCoefficientComparison
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- The actual pulled-back ring object.
Source: the native coefficient convention.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
abbrev coefficient (T : Scheme.{u}) : Mon (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
  coefficientRing T ⟨spIntegralCondensed ell E⟩

/-- Commutativity inherited from the actual pulled-back condensed coefficient ring.
Source: native coefficient convention.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
instance coefficientComm (T : Scheme.{u}) : IsCommMonObj (coefficient ell E T).X := by
  change IsCommMonObj (condensedRingObj (spIntegralCondensed ell E) T)
  infer_instance

/-- The regular native coefficient module in degree zero.
Source: the native-source clause of the current integral comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def unit (T : Scheme.{u}) : Integral ell E T :=
  (DerivedCategory.singleFunctor _ 0).obj
    (Mod.regular (coefficient ell E T).X)
/-- The actual nonnegative power of the inverse-limit root line.
Source: the native-source clause of the current integral comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def rootPower (T : Scheme.{u}) (d : ℕ) :=
  coefficientTwistNat T (coefficient ell E T).X (coefficientIntegralTwistOne ell E T) d
/-- The shifted root-power line.
Source: the native-source clause of the current integral comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def shiftedRootPower (T : Scheme.{u}) (d : ℕ) : Integral ell E T :=
  ((DerivedCategory.singleFunctor _ 0).obj (rootPower ell E T d))⟦(2 * (d : ℤ))⟧
/-- Ordered derived root line, with one even shift per root factor.
This is the usual root-power line shifted by twice its power, with the indicated
parenthesization. Source: native Tate source
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def orderedNative (T : Scheme.{u}) : ℕ → Integral ell E T
  | 0 => unit ell E T
  | d + 1 => orderedNative T d ⊗
      ((DerivedCategory.singleFunctor _ 0).obj (coefficientIntegralTwistOne ell E T))⟦(2 : ℤ)⟧
/-- Native smooth source, in the ordered tensor presentation of the root power.
Source: the native-source clause of the current integral comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def J {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    Integral ell E Y ⥤ Integral ell E X :=
  pull ell E f ⋙ tensorRight (orderedNative ell E X d)
/-- Restrict the same native source to Dbc.
Source: the native-source clause of the current integral comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def Jbc {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (closed : ∀ K : Constructible ell E Y,
      constantModelBoundedConstructible (spIntegralCondensed ell E) X
        ((J ell E f d).obj K.obj)) : Constructible ell E Y ⥤ Constructible ell E X :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (spIntegralCondensed ell E) Y).ι ⋙ J ell E f d) closed

/-- The native reduced source in the ringed-system coordinates, retaining transitions.
Source: the displayed Gamma in the current integral comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def reducedSource (s : Presentation ell E) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    Constructible ell E Y ⥤ SpTowerShriek.D ell E X :=
  (constantModelBoundedConstructible (spIntegralCondensed ell E) Y).ι ⋙ J ell E f d ⋙
    red ell E s X ⋙ (realization ell E s X).functor

/-- A local scalar tensor in the native free module on compatible roots.
Source: the root-limit projection normalization
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def rootTensor (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (a : (coefficient ell E T).X.obj.obj U)
    (z : (Scheme.purTwistZlOne T ell).obj.obj U) :
    ((Mod.freeFunctor (coefficient ell E T).X).obj
      (Scheme.purTwistZlOne T ell)).X.obj.obj U :=
  ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (coefficient ell E T).X (Scheme.purTwistZlOne T ell)).app U) (a ⊗ₜ[ℤ] z)

set_option maxHeartbeats 5000000 in
-- The projection and tensor equations retain full dependent module structures.
/-- Native reduction comparisons fixed on root projections, every scalar tensor,
and K-flat representatives. These are normalizations of actual functors; no source
functor or coefficient unit is supplied as a free parameter.
Source: canonical pullback, root-power and shift identifications in the current item
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
structure NativeReduction (s : Presentation ell E) (T : Scheme.{u})
    (evaluation : Evaluation ell E s) (w : SpChartAdmissibility.Twists ell E T)
    (roots : SpCoordinateAdjunction.RootLines ell E T) where
  tensor : SpNativeIntegralReduction.TensorReduction ell E s T
  rootCoordinates : ∀ n : ℕ,
    Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1)) ≅
      rootsOfUnitySheaf T (ell ^ (n + 1))
  rootCoordinates_sections : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (ell ^ (n + 1))).obj.obj U),
    (rootCoordinates n).hom.hom.app U z =
      (toSheafify (Scheme.ProEt.topology T)
        (rootsOfUnityPresheaf T (ell ^ (n + 1)))).app U
          (ULift.up (Scheme.proEtaleRootsOfUnitySections T (ell ^ (n + 1)) U z))
  generator : (Mod.freeFunctor (coefficient ell E T).X).obj
      (Scheme.purTwistZlOne T ell) ⟶ coefficientIntegralTwistOne ell E T
  projections : ∀ n : ℕ,
    generator.hom ≫ (limit.π (coefficientIntegralTwistSystem ell E T) (op n)).hom =
      coefficientMap (twistReduction ell E n) T ⊗ₘ
        (limit.π (Scheme.proEtaleRootsOfUnityTower T ell (Fact.out : ell.Prime)) (op n) ≫
          (rootCoordinates n).hom)
  ordinaryUnit : (ordinaryReduction ell E s T).obj
      (Mod.regular (coefficient ell E T).X) ≅
        SpTowerClasses.coefficient T (SpTowerClasses.Arings ell E T)
  unit_sections : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (SpTowerShriek.B ell E T n).obj.obj U)
    (a : (coefficient ell E T).X.obj.obj U),
    (((SpTowerShriek.ev ell E T n).map ordinaryUnit.hom).val.app U)
      (((ordinaryReductionEvaluation ell E s evaluation T n).inv.app
        (Mod.regular (coefficient ell E T).X)).val.app U
        (SheafOfModules.systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar ell E T (s.reduction T).coefficient n)).model
          ((spIntegralModuleEquivalence ell E T).functor.obj
            (Mod.regular (coefficient ell E T).X)) U b a)) =
      b * (show (SpTowerShriek.B ell E T n).obj.obj U from
        (spIntegralReductionScalar ell E T (s.reduction T).coefficient n).hom.app U a)
  ordinaryRoot : (ordinaryReduction ell E s T).obj
      (coefficientIntegralTwistOne ell E T) ≅ w.tower 1
  root_sections : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (b : (SpTowerShriek.B ell E T n).obj.obj U)
    (a : (coefficient ell E T).X.obj.obj U)
    (z : (Scheme.purTwistZlOne T ell).obj.obj U),
    (roots.iso n).hom.val.app U ((w.level n 1).hom.val.app U
      ((((SpTowerShriek.ev ell E T n).map ordinaryRoot.hom).val.app U)
        (((ordinaryReductionEvaluation ell E s evaluation T n).inv.app
          (coefficientIntegralTwistOne ell E T)).val.app U
          (SheafOfModules.systemModelTmul ((s.towers T).scalar
            (spIntegralReductionScalar ell E T (s.reduction T).coefficient n)).model
            ((spIntegralModuleEquivalence ell E T).functor.obj
              (coefficientIntegralTwistOne ell E T)) U b
              (generator.hom.hom.app U (rootTensor ell E T U a z)))))) =
      Scheme.tateFiniteTensor T ell (SpTowerClasses.FiniteRing ell E n) n
        (SpTowerClasses.finiteScalar ell E n) U.unop
        (b * (show (SpTowerShriek.B ell E T n).obj.obj U from
        (spIntegralReductionScalar ell E T (s.reduction T).coefficient n).hom.app U a))
        ((limit.π (Scheme.proEtaleRootsOfUnityTower T ell (Fact.out : ell.Prime))
          (op n)).hom.app U z)
  unit_computes : IsIso (reductionComplexComparison ell E s T
    ((CochainComplex.singleFunctor _ 0).obj (Mod.regular (coefficient ell E T).X)))
  root_computes : IsIso (reductionComplexComparison ell E s T
    ((CochainComplex.singleFunctor _ 0).obj (coefficientIntegralTwistOne ell E T)))
  shift : ∀ z : ℤ, shiftFunctor (Integral ell E T) z ⋙ derivedReduction ell E s T ≅
    derivedReduction ell E s T ⋙ shiftFunctor (SpTowerShriek.D ell E T) z
  shift_representatives : ∀ (z : ℤ) (P : CochainComplex (Modules ell E T) ℤ),
    SpNativeIntegralReduction.Good ell E T P →
    (shift z).hom.app (DerivedCategory.Q.obj P) ≫
        (shiftFunctor _ z).map (reductionComplexComparison ell E s T P) =
      (derivedReduction ell E s T).map ((DerivedCategory.Q.commShiftIso z).inv.app P) ≫
        reductionComplexComparison ell E s T (P⟦z⟧) ≫
        DerivedCategory.Q.map
          ((((ordinaryReduction ell E s T).mapHomologicalComplex (.up ℤ)).commShiftIso z).hom.app
            P) ≫
        (DerivedCategory.Q.commShiftIso z).hom.app
          (((ordinaryReduction ell E s T).mapHomologicalComplex (.up ℤ)).obj P)

/-- Localize the normalized ordinary line comparison, using the actual reduction counit.
Source: canonical degree-zero reduction
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def singleReduction (s : Presentation ell E) (T : Scheme.{u})
    (M : Modules ell E T) (N : SpTowerShriek.S ell E T)
    (v : (ordinaryReduction ell E s T).obj M ≅ N)
    (computes : IsIso (reductionComplexComparison ell E s T
      ((CochainComplex.singleFunctor _ 0).obj M))) :
    (derivedReduction ell E s T).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N :=
  letI := computes
  (derivedReduction ell E s T).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M) ≪≫
    asIso (reductionComplexComparison ell E s T ((CochainComplex.singleFunctor _ 0).obj M)) ≪≫
    DerivedCategory.Q.mapIso
      (((ordinaryReduction ell E s T).mapCochainComplexSingleFunctor 0).app M ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso v) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app N).symm

set_option maxHeartbeats 5000000 in
-- The displayed equations expand the actual native derived adjunctions.
/-- Commutativity of the point coefficient object used in scalar comparison.
Source: the continuous coefficient convention.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
instance scalarRingComm : IsCommMonObj (IntegralCoefficientComparison.ring ell E).toMon.X := by
  change IsCommMonObj (spIntegralCondensed ell E)
  infer_instance

/-- Ordinary scalar extension along the actual continuous integer inclusion.
Source: coefficient change, O_E to O_F.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
abbrev ordinaryScalar (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (i : E →ₐ[Padic ell] F) (T : Scheme.{u}) :=
  Mod.extendScalars (coefficientMap
    (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
    (IntegralCoefficientComparison.map ell E F i).hom.hom T)

/-- Scalar comparison on every nonnegative root power, built from the normalized
root-projection map, the multiplication unitor and the ordinary tensorator.
Source: root projections and ordinary-line scalar balancing.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def rootPowerScalar (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (i : E →ₐ[Padic ell] F) (T : Scheme.{u})
    (lines : NativeLines ell E F i T) :
    ∀ d : ℕ, (ordinaryScalar ell E F i T).obj (rootPower ell E T d) ≅
      rootPower ell F T d :=
  letI := Mod.extendScalarsMonoidal (coefficientMap
    (Λ := spIntegralCondensed ell E) (Λ' := spIntegralCondensed ell F)
    (IntegralCoefficientComparison.map ell E F i).hom.hom T)
  Nat.rec (motive := fun d ↦
    (ordinaryScalar ell E F i T).obj (rootPower ell E T d) ≅ rootPower ell F T d)
    (Functor.Monoidal.εIso (ordinaryScalar ell E F i T)).symm
    (fun d previous ↦
      (Functor.Monoidal.μIso (ordinaryScalar ell E F i T)
        (rootPower ell E T d) (coefficientIntegralTwistOne ell E T)).symm ≪≫
          tensorIso previous lines.tate)

/-- The ordinary derived signed-line comparison specialized to the positive power.
The single-functor comparison is the universal derived counit of the exact finite-free
extension; the second arrow is the preceding root-projection construction.
Source: ordinary-line derived scalar comparison.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def derivedRootPowerScalar (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (i : E →ₐ[Padic ell] F) (T : Scheme.{u})
    (lines : NativeLines ell E F i T)
    (flat : PreservesFiniteLimits (ordinaryScalar ell E F i T)) (d : ℕ) :
    (scalar ell E F i T).obj ((DerivedCategory.singleFunctor _ 0).obj
      (rootPower ell E T d)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (rootPower ell F T d) :=
  letI := flat
  ((ordinaryScalar ell E F i T).singleFunctorCompLeftDerivedFunctorIso.app
    (rootPower ell E T d)) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (rootPowerScalar ell E F i T lines d)

/-- Scalar comparison of the ordered native source line, using the coefficient
multiplication unit, each normalized root projection and the standard tensor/shift maps.
Source: the specified q comparison
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def orderedScalar (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (i : E →ₐ[Padic ell] F) (T : Scheme.{u})
    (lines : NativeLines ell E F i T)
    (flat : PreservesFiniteLimits (ordinaryScalar ell E F i T)) : ∀ d : ℕ,
    (scalar ell E F i T).obj (orderedNative ell E T d) ≅ orderedNative ell F T d :=
  letI := flat
  letI := CondensedRing.scalarSixChangeCommShift (IntegralCoefficientComparison.map ell E F i) T
  let root : (scalar ell E F i T).obj
      ((DerivedCategory.singleFunctor _ 0).obj (coefficientIntegralTwistOne ell E T)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (coefficientIntegralTwistOne ell F T) :=
    (ordinaryScalar ell E F i T).singleFunctorCompLeftDerivedFunctorIso.app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso lines.tate
  Nat.rec (motive := fun d ↦
    (scalar ell E F i T).obj (orderedNative ell E T d) ≅ orderedNative ell F T d)
    (derivedRootPowerScalar ell E F i T lines flat 0)
    (fun d previous ↦
      CondensedRing.scalarSixTensorIso (IntegralCoefficientComparison.map ell E F i) T
        (orderedNative ell E T d) _ ≪≫
        tensorIso previous
          (((scalar ell E F i T).commShiftIso (2 : ℤ)).app _ ≪≫
            (shiftFunctor _ (2 : ℤ)).mapIso root))

set_option maxHeartbeats 5000000 in
-- The displayed equations expand the actual native derived adjunctions.
/-- The specified q component: canonical shift comparison, scalar tensor balancing,
cartesian pullback comparison, and the root-projection scalar comparison.
Every arrow is constructed; there is no freely chosen source comparison.
Source: coefficient square of the current item.
(blueprint: lem-pur-general-integral-diagonal-comparison). -/
def sourceScalarComponent (F : Type u) [Field F] [Algebra (Padic ell) F]
    [FiniteDimensional (Padic ell) F] (i : E →ₐ[Padic ell] F)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (lines : NativeLines ell E F i X)
    (flat : ∀ T : Scheme.{u}, PreservesFiniteLimits (ordinaryScalar ell E F i T))
    (K : Integral ell E Y) :
    (scalar ell E F i X).obj ((J ell E f d).obj K) ≅
      (J ell F f d).obj ((scalar ell E F i Y).obj K) :=
  CondensedRing.scalarSixTensorIso (IntegralCoefficientComparison.map ell E F i) X
      ((pull ell E f).obj K) (orderedNative ell E X d) ≪≫
    tensorIso
      ((CondensedRing.derivedPullIso
        (IntegralCoefficientComparison.map ell E F i).hom.hom f).app K)
      (orderedScalar ell E F i X lines (flat X) d)

set_option maxHeartbeats 5000000 in
-- The displayed equations expand the actual native derived adjunctions.
end AlgebraicGeometry.ProEtale.GeneralIntegralDiagonalComparison
