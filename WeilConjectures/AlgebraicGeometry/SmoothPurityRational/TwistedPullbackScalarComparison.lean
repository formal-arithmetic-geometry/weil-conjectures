/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityRational.IntegralTwistedAdjunction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Scalar extension of the signed twisted inverse image

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational.proof.md, first paragraph and last endpoint of its Hom chain.
(blueprint: lem-sp-rational-twisted-pullback-scalar-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityRational

set_option maxHeartbeats 1000000 in
-- Elaborating the section equivalence and derived tensor constraints needs this budget.
/-- The right endpoint comparison in the rational Hom calculation. It involves only
pullback, scalar tensor, the fixed Tate line and shifts; it makes no smoothness or
adjunction assumption. Constructibility of the rational functor is a conclusion.

Source: latest blueprint sk-prop-sp-rational.proof.md, first paragraph and final
endpoint of the displayed Hom chain; sk-prop-sp-rational-adjunction.proof.md (1)
(blueprint: lem-sp-rational-twisted-pullback-scalar-comparison).

Proof: flat scalar extension commutes with the exact cartesian coefficient pullback.
The rational Tate line is by definition the extension of the integral Tate line.
For positive signed powers, compare tensor powers by the monoidal scalar-extension
constraints, starting with the coefficient unitor in degree zero. Transport these
comparisons through the section/internal module equivalence defining the signed
lines. They are natural in the coefficient module. On flat K-flat representatives,
associativity of relative tensor identifies extension of tensor with the degree-zero
integral line with tensor by its rational extension. Localization descends this
chain isomorphism and its inverse to the derived categories. Whisker by inverse
image and then use the exact scalar-extension shift comparison at 2d. This produces
an ambient natural isomorphism J0 QX ≅ QY J, with its maps given by these specified
pullback, tensor and shift comparisons. Every rational bounded constructible object
has an integral model by det-sp-rational-localized-hom. J0 preserves bounded
constructibility by the supplied hG0, and scalar extension preserves it. The ambient
isomorphism, applied to that model and its identification with the original object,
therefore proves that J preserves bounded constructibility. Restrict the ambient
natural isomorphism through the full inclusions to obtain the displayed comparison.
This includes d=0, arbitrary morphisms f, ramified E and the empty scheme. -/
theorem twistedPullbackScalarComparison
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ)
    (hG0 : ∀ K : (boundedConstructible
        (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y.left)).FullSubcategory,
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X.left)
        ((integralAmbientRight l E f d).obj K.obj)) :
    let G :=
      (CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) f.left).mapDerivedCategory ⋙
        tensorRight ((DerivedCategory.singleFunctor _ 0).obj
          (spInternalSignedTwist X.left _ (spRationalTwist X.left l E) (d : ℤ))) ⋙
          shiftFunctor _ (2 * (d : ℤ))
    ∃ hG : ∀ K : (boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)).FullSubcategory,
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)
        (G.obj K.obj),
      Nonempty (integralRight l E f d hG0 ⋙ boundedConstructibleExtendScalars X.left l E ≅
        boundedConstructibleExtendScalars Y.left l E ⋙
          ObjectProperty.lift _
            ((boundedConstructible
              (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)).ι ⋙ G) hG) := by
  classical
  dsimp only
  let FX := Mod.extendScalars (padicIntegersToPadicSubfield X.left l E)
  let FY := Mod.extendScalars (padicIntegersToPadicSubfield Y.left l E)
  let LX := FX.leftDerivedFunctor
  let LY := FY.leftDerivedFunctor
  let U0 := (CondensedRing.upperStar (Profinite.padicIntegersRingObj l E.1)
    f.left).mapDerivedCategory
  let U := (CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
    f.left).mapDerivedCategory
  let T0 := (DerivedCategory.singleFunctor _ 0).obj
    (spInternalSignedTwist X.left _ (spIntegralTwist X.left l E) (d : ℤ))
  let T := (DerivedCategory.singleFunctor _ 0).obj
    (spInternalSignedTwist X.left _ (spRationalTwist X.left l E) (d : ℤ))
  let G := U ⋙ tensorRight T ⋙ shiftFunctor _ (2 * (d : ℤ))
  have : FX.Monoidal := Mod.extendScalarsMonoidal _
  have : LX.Monoidal := FX.leftDerivedFunctorMonoidal
  obtain ⟨eT⟩ := signedTateLineScalarComparison l E X.left d
  have et : tensorRight T0 ⋙ LX ≅ LX ⋙ tensorRight T :=
    (Functor.Monoidal.commTensorRight LX T0).symm ≪≫
      Functor.isoWhiskerLeft LX ((curriedTensor _).flip.mapIso eT)
  have ep : U0 ⋙ LX ≅ LY ⋙ U :=
    Functor.isoWhiskerRight
      (CondensedRing.upperStar (Profinite.padicIntegersRingObj l E.1)
        f.left).leftDerivedFunctorIsoMapDerivedCategory.symm LX ≪≫
    CondensedRing.derivedPullIso
      (padicIntegersRingObjToContinuousMapRingObj l E) f.left ≪≫
    Functor.isoWhiskerLeft LY
      (CondensedRing.upperStar (Profinite.continuousMapRingObj E.1)
        f.left).leftDerivedFunctorIsoMapDerivedCategory
  have a : integralAmbientRight l E f d ⋙ LX ≅ LY ⋙ G :=
    Functor.associator U0 (tensorRight T0) (shiftFunctor _ (2 * (d : ℤ))) |> fun e ↦
    Functor.isoWhiskerRight e LX ≪≫
      Functor.associator U0 _ LX ≪≫
      Functor.isoWhiskerLeft U0
        (Functor.associator (tensorRight T0) _ LX ≪≫
          Functor.isoWhiskerLeft (tensorRight T0) (LX.commShiftIso (2 * (d : ℤ))) ≪≫
          (Functor.associator (tensorRight T0) LX _).symm ≪≫
          Functor.isoWhiskerRight et _) ≪≫
      (Functor.associator U0 (LX ⋙ tensorRight T) _).symm ≪≫
      Functor.isoWhiskerRight
        ((Functor.associator U0 LX _).symm ≪≫ Functor.isoWhiskerRight ep _ ≪≫
          Functor.associator LY U _) _ ≪≫
      Functor.associator LY _ _
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := ⟨⟩
  let QY := boundedConstructibleExtendScalars Y.left l E
  let WY := CategoryTheory.Rationalization.W (Submonoid.powers (l : ℤ))
    (boundedConstructible
      (condensedRingObj (Profinite.padicIntegersRingObj l E.1) Y.left)).FullSubcategory
  have : QY.EssSurj := Localization.essSurj QY WY
  have hG (K : (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)).FullSubcategory) :
      boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)
        (G.obj K.obj) := by
    let K0 := QY.objPreimage K
    let e := (boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)).ι.mapIso
        (QY.objObjPreimageIso K)
    exact ObjectProperty.prop_of_iso _ (a.app K0.obj ≪≫ G.mapIso e)
      (boundedConstructible_derivedExtendScalars_obj X.left l E
        ⟨(integralAmbientRight l E f d).obj K0.obj, hG0 K0⟩)
  refine ⟨hG, ⟨?_⟩⟩
  exact NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ (a.app K.obj))
    (fun h ↦ by
      apply ObjectProperty.hom_ext
      exact a.hom.naturality h.hom)

end AlgebraicGeometry.ProEtale.SmoothPurityRational
