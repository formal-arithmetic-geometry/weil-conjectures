/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicTowerData
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleStalkData
import Submission.WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantGradedModel
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantExtensionTower
import Submission.WeilConjectures.AlgebraicGeometry.FiniteConstantExtensionTower
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantConeStep
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteLocallyConstantWeakSerre
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Submission.WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import Submission.WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Submission.WeilConjectures.CategoryTheory.FiniteTypeConstantLocalLinear
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleHomSurjective
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf
import Submission.WeilConjectures.CategoryTheory.LocalModuleHom
import Submission.WeilConjectures.CategoryTheory.LocalModuleIso
import Submission.WeilConjectures.CategoryTheory.ConstantLocalModuleHom
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleUnit
import Mathlib.Algebra.Module.FinitePresentation
import Submission.WeilConjectures.CategoryTheory.SiteConstantModuleOverHom
import Submission.WeilConjectures.CategoryTheory.FinitePresentationLocalLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.CategoryTheory.Sites.ConstantForget
import Mathlib.RingTheory.Noetherian.Basic
import Submission.WeilConjectures.CategoryTheory.FiniteTypeExtensionLocalPresentation
import Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreeLocalLift
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.ExtensionCokernelPresentation
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.RingTheory.Finiteness.Cardinality
import Submission.WeilConjectures.CategoryTheory.FiniteTypeRestrictionMapExact
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.LinearAlgebra.StdBasis
import Submission.WeilConjectures.AlgebraicGeometry.BoundedTopMorphisms
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.RingTheory.Finiteness.Basic
import Submission.WeilConjectures.AlgebraicGeometry.SiteFiniteConstantComplexDescent
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Additive
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Submission.WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.Algebra.Homology.Homotopy
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Free.FiniteFreeEtaleAcyclicHomotopy
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Submission.WeilConjectures.RingTheory.RingPseudoCoherent
import Submission.WeilConjectures.RingTheory.FiniteFreeResolution
import Submission.WeilConjectures.RingTheory.PseudoCoherentOfCohomology
import Mathlib.Algebra.Homology.Single
import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
import Submission.WeilConjectures.RingTheory.MPseudoCoherentVanishingBase
import Submission.WeilConjectures.RingTheory.PseudoCoherentDistinguishedTriangle
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.LinearAlgebra.Dimension.Free
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.SixFunctors.BaseChange.Pasting
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
import Submission.WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.CoverLifting
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import Submission.WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Submission.WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.SixFunctors.BaseChange.Square
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Prod
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantSheafStalk
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Submission.WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheaf
import Submission.WeilConjectures.ConstructibleSheaf.InternalHom
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition
import all Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Scalar realizations of ordinary fixed-scalar coordinates

The explicit scalar realization of the fixed-scalar coordinates of a module sheaf is the
restriction of the module sheaf to the slice.

Source: Stacks Project, Tags 03CY, 03DA and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

section Associated

variable {C : Type (t + 1)} [Category.{t} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{t + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t + 1}]
  {B : Type (t + 1)} [CommRing B] {R : Sheaf J RingCat.{t + 1}}
  (α : (Functor.const Cᵒᵖ).obj (RingCat.of B) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

end Associated

section Realization

set_option hygiene false in
local notation "𝓡" R => (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

variable (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U)

/-- Restriction from the chart to `W`, followed by transport to the slice. -/
def finitePerfectAdicChartSlice (Q : Type (t + 1)) [CommRing Q] :
    Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} Q) ⥤
      Sheaf ((ProEt.topology X).over W) (ModuleCat.{t + 1} Q) :=
  have := ProEt.sliceDense X W
  ProEtale.localizationRestriction (ModuleCat.{t + 1} Q) f.left
      (finitePerfectAdicChartArrow_weaklyEtale V U W f) ⋙
    ((ProEt.sliceEquiv X W).sheafCongr ((ProEt.topology X).over W)
      (ProEt.topology W.left) (ModuleCat.{t + 1} Q)).inverse

/-- The explicit scalar realization for an arbitrary locally bijective fixed-scalar
presentation of a ring sheaf on the slice and an arbitrary map of ring sheaves. -/
def finitePerfectAdicRealizationModules {Q : Type (t + 1)} [CommRing Q]
    {R T : Sheaf (ProEt.topology X) RingCat.{t + 1}}
    (αW : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of Q) ⟶ (R.over W).obj)
    [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW]
    [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW] (π : T ⟶ R) :
    Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} Q) ⥤ SheafOfModules.{t + 1} (T.over W) :=
  finitePerfectAdicChartSlice X V U W f Q ⋙ finitePerfectAdicAssociated αW ⋙
    SheafOfModules.restrictScalars (((ProEt.topology X).overPullback RingCat.{t + 1} W).map π)

/-- The object of the pro-etale site of `X` underlying an object of the slice at `W`, seen
through the chart. -/
def finitePerfectAdicChartImage (Z : Over W) : X.ProEt :=
  (MorphismProperty.Over.map ⊤ (show WeaklyEtale V.hom from inferInstance)).obj
    ((MorphismProperty.Over.map ⊤ U.prop).obj
      ((MorphismProperty.Over.map ⊤ (finitePerfectAdicChartArrow_weaklyEtale V U W f)).obj
        ((ProEt.sliceEquiv X W).functor.obj Z)))

/-- An object of the slice at `W` maps to its image through the chart, by the identity of
its underlying scheme. -/
def finitePerfectAdicChartPointIso (Z : Over W) :
    Z.left ≅ finitePerfectAdicChartImage X V U W f Z :=
  MorphismProperty.Over.isoMk (Iso.refl Z.left.left) (by
    have h₁ : Z.hom.left ≫ W.hom = Z.left.hom := MorphismProperty.Over.w Z.hom
    have h₂ : f.left ≫ (finitePerfectAdicChartObject V U).hom = W.hom :=
      MorphismProperty.Over.w f
    change 𝟙 _ ≫ ((Z.hom.left ≫ f.left) ≫ U.hom) ≫ V.hom = Z.left.hom
    rw [Category.id_comp, ← h₁, ← h₂]
    simp [finitePerfectAdicChartObject])

/-- An object of the slice at `W` maps to its image through the chart. -/
abbrev finitePerfectAdicChartPoint (Z : Over W) :
    Z.left ⟶ finitePerfectAdicChartImage X V U W f Z :=
  (finitePerfectAdicChartPointIso X V U W f Z).hom

variable {B : Type t} [CommRing B] (Rc : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
  (φ : adicConstantRing X B ⟶ Rc)
  (αW : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B)) ⟶ ((𝓡 Rc).over W).obj)

/-- The fixed-scalar coordinates of a module sheaf on the chart, restricted to `W` and
transported to the slice. -/
abbrev finitePerfectAdicChartModule (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    Sheaf ((ProEt.topology X).over W) (ModuleCat.{t + 1} (ULift.{t + 1} B)) :=
  (finitePerfectAdicChartSlice X V U W f (ULift.{t + 1} B)).obj
    ((ProEtale.localizationRestriction (ModuleCat.{t + 1} (ULift.{t + 1} B)) U.hom U.prop).obj
      ((finiteCoefficientSliceRestriction X B Rc φ V).obj M))

/-- The fixed-scalar coordinates of a module sheaf on the chart, restricted to `W`, map to the
restriction of the module sheaf to `W` by restriction along the chart points. -/
def finitePerfectAdicChartRestriction
    (hα : ∀ (Z : Over W) (c : ULift.{t + 1} B),
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
        φ).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B).app (op Z.left) c) =
        αW.app (op Z) c)
    (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    (ProEtale.finiteCoefficientModulePresheaf (Over W) (ULift.{t + 1} B)).obj
        ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M)) ⟶
      (PresheafOfModules.restrictScalars αW).obj
        ((SheafOfModules.forget _).obj ((SheafOfModules.overFunctor (𝓡 Rc) W).obj M)) :=
  PresheafOfModules.homMk (M₁ := (ProEtale.finiteCoefficientModulePresheaf (Over W)
      (ULift.{t + 1} B)).obj
        ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M)))
    (M₂ := (PresheafOfModules.restrictScalars αW).obj
        ((SheafOfModules.forget _).obj ((SheafOfModules.overFunctor (𝓡 Rc) W).obj M)))
    { app := fun Z ↦ M.val.presheaf.map (finitePerfectAdicChartPoint X V U W f Z.unop).op
      naturality := by
        intro Z₁ Z₂ k
        change M.val.presheaf.map _ ≫ M.val.presheaf.map _ =
          M.val.presheaf.map _ ≫ M.val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1 }
    (by
      intro Z c x
      change M.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op
          (((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
            φ).hom.app (op (finitePerfectAdicChartImage X V U W f Z.unop))
              ((proEtaleModuleScalarUnit X B).app _ c) •
            (show M.val.obj (op (finitePerfectAdicChartImage X V U W f Z.unop)) from x)) =
        αW.app Z c • (show M.val.obj (op Z.unop.left) from
          M.val.map (finitePerfectAdicChartPoint X V U W f Z.unop).op x)
      rw [PresheafOfModules.map_smul, ← hα]
      congr 1
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
      rfl)

variable [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW]
  (hα : ∀ (Z : Over W) (c : ULift.{t + 1} B),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B).app (op Z.left) c) =
      αW.app (op Z) c)

/-- The associated module sheaf of the fixed-scalar coordinates of a module sheaf, restricted to
`W`, maps to the restriction of the module sheaf, by the adjoint of restriction along the chart
points. -/
def finitePerfectAdicChartAssociated (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    (finitePerfectAdicAssociated αW).obj (finitePerfectAdicChartModule X V U W f Rc φ M) ⟶
      (SheafOfModules.overFunctor (𝓡 Rc) W).obj M :=
  (PresheafOfModules.sheafificationHomEquiv αW).symm
    (finitePerfectAdicChartRestriction X V U W f Rc φ αW hα M)

/-- Before associated sheafification, the chart comparison is restriction along the chart
points. -/
theorem finitePerfectAdicChartAssociated_unit (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    toSheafify ((ProEt.topology X).over W)
        ((ProEtale.finiteCoefficientModulePresheaf (Over W) (ULift.{t + 1} B)).obj
          ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M))).presheaf ≫
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)) =
      (PresheafOfModules.toPresheaf _).map
        (finitePerfectAdicChartRestriction X V U W f Rc φ αW hα M) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def αW
    (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)
  unfold finitePerfectAdicChartAssociated at h ⊢
  simp only [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The fixed-scalar coordinates are already a sheaf. -/
instance finitePerfectAdicChartModule_isIso_toSheafify (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    IsIso (toSheafify ((ProEt.topology X).over W)
      ((ProEtale.finiteCoefficientModulePresheaf (Over W) (ULift.{t + 1} B)).obj
        ((sheafToPresheaf _ _).obj (finitePerfectAdicChartModule X V U W f Rc φ M))).presheaf) := by
  apply isIso_toSheafify
  exact ((sheafCompose ((ProEt.topology X).over W)
    (forget₂ (ModuleCat.{t + 1} (ULift.{t + 1} B)) AddCommGrpCat.{t + 1})).obj
      (finitePerfectAdicChartModule X V U W f Rc φ M)).property

/-- The chart comparison is an isomorphism, since restriction along the chart points is. -/
instance finitePerfectAdicChartAssociated_isIso (M : SheafOfModules.{t + 1} (𝓡 Rc)) :
    IsIso (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M) := by
  have := finitePerfectAdicChartModule_isIso_toSheafify X V U W f Rc φ M
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map
      (finitePerfectAdicChartRestriction X V U W f Rc φ αW hα M)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    change IsIso (M.val.presheaf.map (finitePerfectAdicChartPoint X V U W f Z.unop).op)
    infer_instance
  rw [← finitePerfectAdicChartAssociated_unit] at h₂
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
      (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M))) :=
    IsIso.of_isIso_comp_left (toSheafify _ _) _
  have : IsIso ((SheafOfModules.forget _).map
      (finitePerfectAdicChartAssociated X V U W f Rc φ αW hα M)) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _)

variable {T : Sheaf (ProEt.topology X) RingCat.{t + 1}} (π : T ⟶ 𝓡 Rc)

end Realization

section Square

set_option hygiene false in
local notation "𝓡" R => (sheafCompose (ProEt.topology X)
  (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R

variable (X : Scheme.{t}) (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U)
  {B₁ B₀ : Type t} [CommRing B₁] [CommRing B₀] (q : B₁ →+* B₀)
  {Rc₁ Rc₀ : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (s : Rc₁ ⟶ Rc₀)
  (φ₁ : adicConstantRing X B₁ ⟶ Rc₁) (φ₀ : adicConstantRing X B₀ ⟶ Rc₀)
  (αW₁ : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B₁)) ⟶ ((𝓡 Rc₁).over W).obj)
  (αW₀ : (Functor.const (Over W)ᵒᵖ).obj (RingCat.of (ULift.{t + 1} B₀)) ⟶ ((𝓡 Rc₀).over W).obj)
  [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW₁]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW₁]
  [Presheaf.IsLocallyInjective ((ProEt.topology X).over W) αW₀]
  [Presheaf.IsLocallySurjective ((ProEt.topology X).over W) αW₀]
  (hα₁ : ∀ (Z : Over W) (c : ULift.{t + 1} B₁),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ₁).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B₁).app (op Z.left) c) =
      αW₁.app (op Z) c)
  (hα₀ : ∀ (Z : Over W) (c : ULift.{t + 1} B₀),
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      φ₀).hom.app (op Z.left) ((proEtaleModuleScalarUnit X B₀).app (op Z.left) c) =
      αW₀.app (op Z) c)
  (p : (𝓡 Rc₁) ⟶ (𝓡 Rc₀))
  (hps : (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map s = p)
  (hαp : ∀ Z, αW₁.app Z ≫ (((ProEt.topology X).overPullback RingCat.{t + 1} W).map p).hom.app Z =
    RingCat.ofHom (RingHom.ulift q) ≫ αW₀.app Z)
  {T : Sheaf (ProEt.topology X) RingCat.{t + 1}} (π₁ : T ⟶ 𝓡 Rc₁) (π₀ : T ⟶ 𝓡 Rc₀)
  (hπ : π₁ ≫ (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    s = π₀)
  (coh : sheafCompose (ProEt.topology U.left)
      (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q)) ⋙
      finitePerfectAdicRealizationModules X V U W f αW₁ π₁ ≅
    finitePerfectAdicRealizationModules X V U W f αW₀ π₀)
  (hcoh : ∀ G : Sheaf (ProEt.topology U.left) (ModuleCat.{t + 1} (ULift.{t + 1} B₀)),
    (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map (coh.hom.app G)) =
      (PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map
        ((finitePerfectAdicAssociatedCoherence αW₁ αW₀ (RingHom.ulift.{t + 1, t + 1} q)
          (((ProEt.topology X).overPullback RingCat.{t + 1} W).map p) hαp).hom.app
          ((finitePerfectAdicChartSlice X V U W f _).obj G))))
  {M₁ : SheafOfModules.{t + 1} (𝓡 Rc₁)} {M₀ : SheafOfModules.{t + 1} (𝓡 Rc₀)}
  (g : M₁ ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      s)).obj M₀)
  (δ : (finiteCoefficientSliceRestriction X B₁ Rc₁ φ₁ V).obj M₁ ⟶
    (sheafCompose (ProEt.topology V.left)
      (ModuleCat.restrictScalars.{t + 1} (RingHom.ulift q))).obj
        ((finiteCoefficientSliceRestriction X B₀ Rc₀ φ₀ V).obj M₀))
  (hδ : ∀ (U' : V.left.ProEt) x, δ.hom.app (op U') x =
    g.val.app (op (finitePerfectAdicChartObject V U')) x)

end Square

end AlgebraicGeometry.Scheme
