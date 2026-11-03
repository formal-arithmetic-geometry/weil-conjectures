/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import WeilConjectures.AlgebraicGeometry.Curve.FLCFiber
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Separable
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import Mathlib.CategoryTheory.Filtered.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import WeilConjectures.AlgebraicGeometry.IntermediateFieldLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentLisse
import WeilConjectures.AlgebraicGeometry.LisseFiniteDescent
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealSheavesSetup
public import WeilConjectures.WeilSheaf.RealSheaves.Setup.RealWeilSheaves
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedLisseMonodromy
public import WeilConjectures.AlgebraicGeometry.EtaleAdicPathData
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverLift
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.StalkTransport
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.LisseQlbar.LisseQlbarRepresentations
public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy.CondensedMonodromyFrobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Compactification.GeometricallyConnectedAlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.RealCondensedFibre.RealCondensedFibreFunctoriality
public import WeilConjectures.GroupTheory.WeilGroup
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.RealWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldSmoothDuality.CondensedFieldSmoothDuality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeOfFinitelyPresented.Sections
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.AlgebraicGeometry.CondensedLisseRankLoci
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricSpecializationStrictLocalLift
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
public import WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughImmersion
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleInverseImageStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientSectionsLocalization
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarMatrixInverseImage
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Separation
public import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.RingTheory.ProEtale.PullbackProfinite
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WeakDimension
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.ProperBaseChange.GeometricFieldProfiniteDenseSubsite
public import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointDiscreteConstantComparison
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsOfIsIso
public import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import Mathlib.RepresentationTheory.Coinvariants

/-! # Degree zero and top compactly supported cohomology

Source: latest blueprint, sk-lem-wrp-hc2 (blueprint: sk-lem-wrp-hc2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open RealSheaves.Condensed
open WeilConjectures.CondensedWeil
open WeilConjectures
open scoped CategoryTheory.Obj

namespace RealSheaves.Condensed

/-- The unit vector in the actual geometric fibre, using the canonical pullback unit map.
Source: p-real-sections.proof.md, evaluation at one (blueprint: sk-lem-wrp-hc2). -/
def sectionUnitVector (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) :
    (LisseQlbar.fibre (Profinite.padicAlgClRingObj l) x).obj
      (𝟙_ (RealCondensedFibre.Modules (Profinite.padicAlgClRingObj l) X)) :=
  ((Evaluation.sections (Scheme.ProEt.topology (Spec (.of Ω)))
    (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of Ω)))
      (Scheme.ProEt.mk (𝟙 _))).map
        (upperStarObjRegularIso (Profinite.padicAlgClRingObj l) x).inv).hom
      (1 : Evaluation.A (Scheme.ProEt.topology (Spec (.of Ω)))
        (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of Ω)))
          (Scheme.ProEt.mk (𝟙 _)))

/-- Pull back a literal module section and evaluate it at the coefficient unit vector.
Source: p-real-sections.md, geometric generic germ (blueprint: sk-lem-wrp-hc2). -/
def nativeSectionGerm (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X)
    (M : RealCondensedFibre.Modules (Profinite.padicAlgClRingObj l) X)
    (b : 𝟙_ _ ⟶ M) : (LisseQlbar.fibre (Profinite.padicAlgClRingObj l) x).obj M :=
  ((LisseQlbar.fibre (Profinite.padicAlgClRingObj l) x).map b).hom
    (sectionUnitVector l x)

/-- The actual section Frobenius is pullback by geometric Frobenius followed by phi.
Source: p-real-sections.md, residual action (blueprint: sk-lem-wrp-hc2). -/
def nativeSectionFrobenius (D : Setup.{u, v}) (X₀ : Over (Spec (.of D.k₀)))
    (L : LisseWeil (Profinite.padicAlgClRingObj D.l) (frobenius D X₀))
    (b : 𝟙_ _ ⟶ L.obj.carrier) : 𝟙_ _ ⟶ L.obj.carrier :=
  (upperStarObjRegularIso (Profinite.padicAlgClRingObj D.l) (frobenius D X₀).hom).inv ≫
    (upperStar (Profinite.padicAlgClRingObj D.l) (frobenius D X₀).hom).map b ≫
      L.obj.str.hom

end RealSheaves.Condensed

namespace RealSheaves

/-- A literal dual section acts by the actual internal-Hom evaluation.
Source: sk-lem-wrp-hc2.proof.md, the annihilator identification
(blueprint: sk-lem-wrp-hc2). -/
def endpointEvaluation (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (M : FieldSmoothDuality.coefficientModule l X)
    (b : 𝟙_ _ ⟶ FieldSmoothDuality.dual l X M) : M ⟶ 𝟙_ _ :=
  (ρ_ M).inv ≫ (M ◁ b) ≫ (ihom.ev M).app (𝟙_ _)

open AlgebraicGeometry.ProEtale.CondensedLisseMonodromy

end RealSheaves
