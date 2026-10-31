/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.ContinuousMap.Compact
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact

import WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import all WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.ConstructibleSheaf.OpenClosed
import all WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Derived image comparison for localization of an integral heart model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

private def singleIntegralModel (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hN : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X) N) :
    integralConstructible ℓ E X :=
  ⟨(DerivedCategory.singleFunctor _ 0).obj N, by
    rw [ProEtale.mem_boundedConstructible_iff]
    refine ⟨⟨0, 0, ?_⟩, ?_⟩
    · intro i hi
      rcases hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    · intro i
      rcases eq_or_ne i 0 with rfl | hi
      · exact _root_.constructible_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app N).symm hN
      · rcases lt_or_gt_of_ne hi with hi | hi
        · exact ProEtale.constructible_of_isZero _ _
            (DerivedCategory.isZero_of_isGE _ 0 i hi)
        · exact ProEtale.constructible_of_isZero _ _
            (DerivedCategory.isZero_of_isLE _ 0 i hi)⟩

set_option maxHeartbeats 800000 in
-- The derived scalar transport proof needs extra reduction heartbeats.
/-- Flat localization commutes with both native images of an integral sheaf, including
transport between the continuous and spectral presentations of the integer ring.
No dimension or cohomological bound is asserted.

Source: current blueprint, sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
E-coefficient paragraph of the Complement; sk-prop-scalar-six.
(blueprint: lem-sf-finite-point-integral-scalar-images).

Proof in words. Restriction along the inverse of e identifies the continuous integral
model N with a spectral integral model. Since e is an isomorphism of coefficient rings,
this is an exact equivalence. Its inverse is restriction along e, and the two restriction
functors commute with ordinary direct image: the right-adjoint mate of the coefficient
pullback square is the canonical comparison. They also commute with extension by zero:
the open-immersion adjunction gives the inverse mate, normalized by its unit. Consequently
the spectral native images become the continuous integral native images under restriction
along e. This assertion holds in the specified compactification, not just a chosen one.
Next express E as the localization of its valuation ring by ell. On compact profinite
tests, one power of ell clears the denominators of every continuous function. Pullback
and tensor commute with this sequential colimit, and filtered colimits are exact, so the
localization functor is exact. For ordinary image use bounded-below qcqs continuity to
commute derived pushforward with this telescope; its mate is integralScalarPushHom.
For compact image write it as Rg_* j_!: j_! is exact, preserves constructibility and
commutes with localization by the normalized open mate, and the same telescope comparison
applies to the proper g. The input N[0] and j_!N[0] are bounded constructible, so these
comparisons are invertible. Compose these derived comparisons with the two image maps
induced by the single-complex form of the specified model isomorphism m. This gives the two
displayed isomorphisms in the derived category. Zero modules and empty schemes use the
same zero-object comparisons. -/
theorem finite_point_integral_scalar_images
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (e : Mon.mk (integralCoeff.{u} ℓ E) ≅
      Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} E)))
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom)
    (N : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X.left))
    (hN : IsConstructibleModuleObject (condensedRingObj (integralCoeff ℓ E) X.left) N)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left))
    (m : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X.left)).obj N ≅ M) :
    let N' := (Mod.comap (coefficientMap e.inv.hom X.left)).obj N
    let R := Mod.comap
      (D := Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
      (coefficientMap e.hom.hom (Spec (.of D.k)))
    let T := Mod.extendScalars
      (coefficientMap (integralScalarMap ℓ E) (Spec (.of D.k)))
    Nonempty (T.leftDerivedFunctor.obj (R.mapDerivedCategory.obj
      ((rightDerivedLowerShriekOfCompactification
        (DerivedNakayama.integerRing ℓ (ULift.{u} E)) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj N'))) ≅
      (rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj.{u} E) c).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
    Nonempty (T.leftDerivedFunctor.obj (R.mapDerivedCategory.obj
      ((lowerStar (DerivedNakayama.integerRing ℓ (ULift.{u} E)) X.hom).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj N'))) ≅
      (lowerStar (Profinite.continuousMapRingObj.{u} E) X.hom).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let A := integralCoeff.{u} ℓ E
  let O := DerivedNakayama.integerRing ℓ (ULift.{u} E)
  let B := Profinite.continuousMapRingObj.{u} E
  let R (Z : Scheme.{u}) :=
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap e.hom.hom Z)
  let N' := (Mod.comap (coefficientMap e.inv.hom X.left)).obj N
  let K' := (DerivedCategory.singleFunctor _ 0).obj N'
  let K := (DerivedCategory.singleFunctor _ 0).obj N
  have (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.hom.hom Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let en : (R X.left).obj N' ≅ N :=
    ((Mod.comapComp (coefficientMap e.hom.hom X.left)
        (coefficientMap e.inv.hom X.left)).symm ≪≫
      Mod.comapCongr (by
        change (upperStarFromPoint X.left).map e.hom.hom ≫
          (upperStarFromPoint X.left).map e.inv.hom = 𝟙 _
        rw [← Functor.map_comp]
        have he : e.hom.hom ≫ e.inv.hom = 𝟙 _ := by
          exact congrArg (fun z ↦ z.hom) e.hom_inv_id
        rw [he, CategoryTheory.Functor.map_id]) ≪≫ Mod.comapId _).app N
  let ek : (R X.left).mapDerivedCategory.obj K' ≅ K :=
    ((R X.left).mapDerivedCategorySingleFunctor 0).app N' ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso en
  let erOpen := (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek O c.i) (R c.Z)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (comapOpenImmersionLowerShriekIso e.hom.hom c.i) ≪≫
    Functor.mapDerivedCategoryCompIso (R X.left) (openImmersionLowerShriek A c.i)
  let erc := (derivedComapLowerStarIso e.hom.hom c.g).app
      ((openImmersionLowerShriek O c.i).mapDerivedCategory.obj K') ≪≫
    (lowerStar A c.g).rightDerivedFunctor.mapIso (erOpen.app K') ≪≫
    (rightDerivedLowerShriekOfCompactification A c).mapIso ek
  let ero := (derivedComapLowerStarIso e.hom.hom X.hom).app K' ≪≫
    (lowerStar A X.hom).rightDerivedFunctor.mapIso ek
  let a := integralScalarMap ℓ E
  let TX := Mod.extendScalars (coefficientMap a X.left)
  let TY := Mod.extendScalars (coefficientMap a (Spec (.of D.k)))
  let J := openImmersionLowerShriek A c.i
  let eJ := (J.mapDerivedCategorySingleFunctor 0).app N
  have hJN := (singleIntegralModel ℓ E c.Z (J.obj N)
    (isConstructibleModuleObject_openImmersionLowerShriek A c.i N hN)).property
  let KJ : integralConstructible ℓ E c.Z := ⟨J.mapDerivedCategory.obj K, by
    rw [mem_boundedConstructible_iff] at hJN ⊢
    obtain ⟨⟨a, b, hv⟩, hc⟩ := hJN
    refine ⟨⟨a, b, fun q hq ↦ ?_⟩, fun q ↦ ?_⟩
    · exact (hv q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso eJ)
    · exact _root_.constructible_of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso eJ).symm (hc q)⟩
  have : IsIso ((derivedPushHom a X.hom).app K) :=
    integralScalarPushHom_isIso ℓ E X.hom (singleIntegralModel ℓ E X.left N hN)
  have : IsIso ((derivedPushHom a c.g).app KJ.obj) :=
    integralScalarPushHom_isIso ℓ E c.g KJ
  let eK : TX.leftDerivedFunctor.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj M :=
    TX.singleFunctorCompLeftDerivedFunctorIso.app N ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso m
  let ec := asIso ((derivedPushHom a c.g).app KJ.obj) ≪≫
    (lowerStar B c.g).rightDerivedFunctor.mapIso
      ((derivedOpenImmersionShriekIso a c.i).app K) ≪≫
    (rightDerivedLowerShriekOfCompactification B c).mapIso eK
  let eo := asIso ((derivedPushHom a X.hom).app K) ≪≫
    (lowerStar B X.hom).rightDerivedFunctor.mapIso eK
  exact ⟨⟨TY.leftDerivedFunctor.mapIso erc ≪≫ ec⟩,
    ⟨TY.leftDerivedFunctor.mapIso ero ≪≫ eo⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
