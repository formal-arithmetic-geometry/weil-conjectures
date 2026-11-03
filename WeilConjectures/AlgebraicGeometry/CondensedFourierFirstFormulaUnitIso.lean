/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedFourierFirstFormulaMembership
import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePointSectionsConservative
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.CharacterIntegral.CharacterIntegralTrace
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
import WeilConjectures.AlgebraicGeometry.ArtinSchreierUnit.ArtinSchreierUnitTrivialization
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CompletedLimitBridge
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1LocalizingPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalAffineTensorCalculus
import WeilConjectures.Algebra.Homology.Signed.SignedLineEvaluation
import WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.CharacterIntegral.NativeLinearCharacterVanishing
import WeilConjectures.AlgebraicGeometry.CharacterIntegral.RationalCoordinateTracePurity
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.AlgebraicGeometry.CondensedFourierKernelCoefficientComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
import Mathlib.CategoryTheory.Monoidal.CommMon_
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.SheafTensor
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.NoetherianStratumDetectionSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
import WeilConjectures.AlgebraicGeometry.CondensedFourierUnitZeroCompactSupport
import Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTatePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalLocalizingProjectionFormula
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarDescent
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.LocallyConstantPerfectComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CtfLocallyClosedPerfectGeneration
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.InternalHomDualTorAmplitude
import WeilConjectures.Algebra.Homology.Monoidal.Dual
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateData
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeProperScalarMateData
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureOrdinaryLine
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward

/-! # One calculation in the first Fourier formulas

Source: current blueprint, lem-fd-first-formula.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The constant-unit Fourier comparisons for both coefficient models.

Source: current blueprint, first-formula proof, constant-sheaf paragraph
(blueprint: lem-fd-first-formula-unit-iso).

Proof in words. First work over k₀ with finite-intermediate-field coefficients. Expanding
the transform of the unit gives the compact-support direct image of the kernel shifted by
one. At every nonzero geometric point the stalk formula and nontrivial character integral
make this object zero. Its restriction to the punctured line is bounded constructible, so
geometric-fibre conservativity makes that restriction zero. The ordinary open-closed
localization triangle then identifies the transform with the closed direct image of its
ordinary restriction to zero. Shriek base change at zero and the zero-function
Artin-Schreier unit trivialization identify that restriction with the compact-support
cohomology of the affine line shifted by one. The rational affine-line trace over k₀ is the
negative Tate line shifted by minus two; after the Fourier shift it is shifted by minus one.
The closed support projection formula moves the Tate line through the zero-section direct
image, yielding the signed twist of the skyscraper. Pull this comparison to k by arbitrary
base-map compact-support exchange; coefficient and monoidal pullback comparisons identify
the displayed objects. Finally extend coefficients to the finite-subextension algebraic
closure. Scalar comparisons commute with all the operations and with the character
projector on the finite etale torsor pushforward, hence preserve the actual kernel and Tate
line. This gives the second displayed comparison without any choice of a trivial Tate line.
-/
theorem first_formula_unit_iso
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  Nonempty ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀ k
        ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
        ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) ∧
  Nonempty ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
      ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))) ≅
    (shiftFunctor _ (-1 : ℤ)).obj
      (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spQbarTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ)
        ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))))
        (-1))) := by
  obtain ⟨hE, hQ⟩ := first_formula_unit_punctured_vanishing p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  obtain ⟨⟨eE⟩, ⟨eQ⟩⟩ := first_formula_unit_closed_fiber p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  let i := AffineSpace.zeroSection PUnit (Spec (.of k))
  let U := i.openComplement
  have : IsLocallyNoetherian (AffineSpace PUnit (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
  have hij : IsCompl (Set.range i.base) (Set.range U.ι.base) := by
    dsimp only [U]
    rw [i.range_eq_compl_range_openComplement_ι]
    exact isCompl_compl.symm
  constructor
  · have h := CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero
      (Profinite.continuousMapRingObj E.1) U.ι i hij hE
    exact ⟨@asIso _ _ _ _ _ h ≪≫ eE⟩
  · have h := CondensedRing.isIso_derivedUpperStarLowerStarAdjunction_unit_app_of_isZero
      (Profinite.padicAlgClRingObj ℓ) U.ι i hij hQ
    exact ⟨@asIso _ _ _ _ _ h ≪≫ eQ⟩

end AlgebraicGeometry.ProEtale
