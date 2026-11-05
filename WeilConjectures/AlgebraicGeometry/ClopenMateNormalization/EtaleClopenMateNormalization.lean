/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenInterchangeData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Proper
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.SmoothPurity.ClopenMateComposite
import WeilConjectures.CategoryTheory.Derived.DerivedExactMateSupplement
import WeilConjectures.CategoryTheory.Derived.DerivedComplexUnitCompatibility
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Proper-support normalization of the finite etale clopen mate

Source: Stacks Project, More on Etale Cohomology, Tag 0F7B,
first paragraph of the proof of lemma-shriek-proper-and-open
(blueprint: lem-cbc-etale-clopen-mate-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctorPlus

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
namespace ClopenMateNormalization

section DerivedMate

open CategoryTheory.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [HasKInjectiveResolutions C₁] [HasKInjectiveResolutions C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- Exact localization of a natural-transformation square, retaining the canonical
composition comparisons. Source: Stacks Tags 015F and 070K
(blueprint: def-cbc-localized-clopen-square). -/
@[no_expose, irreducible] def clopenLocalizedSquare (σ : G ⋙ L' ⟶ L ⋙ G') :
    G.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ G'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso G L').inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso C₂ (.up ℤ)) _ _ _ _
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex σ (.up ℤ)) DerivedCategory.Q) ≫
    (Functor.mapDerivedCategoryCompIso L G').hom

section Plus
variable [EnoughInjectives C₁] [EnoughInjectives C₃]

/-- Exact localization of a natural-transformation square, retaining the canonical
composition comparisons. Source: Stacks Tags 015F and 070K
(blueprint: def-cbc-localized-clopen-square). -/
@[no_expose, irreducible] def clopenLocalizedSquarePlus (σ : G ⋙ L' ⟶ L ⋙ G') :
    G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ⟶
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus :=
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂)
      ((G ⋙ L').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (G ⋙ L').mapDerivedCategoryPlus := ⟨(G ⋙ L').mapDerivedCategoryPlusFactorsh⟩
  letI : Localization.Lifting DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂)
      ((L ⋙ G').mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (L ⋙ G').mapDerivedCategoryPlus := ⟨(L ⋙ G').mapDerivedCategoryPlusFactorsh⟩
  (Functor.mapDerivedCategoryPlusCompIso G L').inv ≫
    Localization.liftNatTrans DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C₂) _ _ _ _
      (Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus σ) DerivedCategory.Plus.Qh) ≫
    (Functor.mapDerivedCategoryPlusCompIso L G').hom

end Plus

section Ambient
variable [EnoughInjectives C₁] [EnoughInjectives C₃]

end Ambient

end DerivedMate

variable (Λ : Type (u + 1)) [CommRing Λ]

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  upperStarLowerStarAdjunction openImmersionLowerShriekUpperStarAdjunction

/-- The prescribed composite of cartesian open base change, the clopen projection,
and the canonical open-extension and inverse-image compositors.
Source: Stacks Tag 0F7B, first proof paragraph
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def alpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⋙
        upperStar (ModuleCat.{u + 1} Λ) p ⟶
      upperStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k :=
  let s := pullback.lift k r h
  letI := (lift_clopen k r p i h).1
  letI := (lift_clopen k r p i h).2
  let q := pullback.snd p i
  let b := pullback.fst p i
  CategoryTheory.clopenMateComposite
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)
    (upperStar (ModuleCat.{u + 1} Λ) p)
    (upperStar (ModuleCat.{u + 1} Λ) q)
    (upperStar (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)
    (upperStar (ModuleCat.{u + 1} Λ) r)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} Λ) (IsPullback.of_hasPullback p i).flip)).inv
    (projection Λ s)
    ((openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) s b).inv ≫
      (openCongr Λ (pullback.lift_fst k r h)).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) s q).inv ≫
      (eqToIso (congrArg (upperStar (ModuleCat.{u + 1} Λ))
        (pullback.lift_snd k r h))).hom)

/-- The ordinary proper-adjunction mate of the specified clopen comparison.
Source: Stacks Tag 0F7B (blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def mate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) (alpha Λ k r p i h)

/-- Exact localization of the specified alpha, on the ordinary derived categories.
Source: Stacks Tags 015F and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def derivedAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory :=
  clopenLocalizedSquare (alpha Λ k r p i h)

/-- Restriction of the exact localization of alpha to bounded-below objects.
Source: Stacks Tags 015F and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def derivedAlphaPlus {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategoryPlus ⟶
      (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus :=
  clopenLocalizedSquarePlus (alpha Λ k r p i h)

/-- The actual proper mate, using the unbounded derived adjunction induced by the
ordinary inverse-image/direct-image adjunction.
Source: Stacks Tags 0F7B and 070K
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def derivedMate {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctor ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategory ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) p).rightDerivedFunctor :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedAlpha Λ k r p i h)).natTrans

/-- The support-preserving comparison selected from the recorded coherence theorem.
Its inclusion into (ir)_* = (pk)_* retains every section, uniquely determining it.
Source: Stacks Tags 0F50, 0F51 and 0F7B
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def supportComparison [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    lowerStar (ModuleCat.{u + 1} Λ) r ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k ⋙
        lowerStar (ModuleCat.{u + 1} Λ) p :=
  (properOpenInterchangeData Λ).underived k i r p h

/-- The degreewise support identification, followed by the specified p_*t.
Source: Stacks Tag 0F7B, the displayed chain map in its first proof paragraph
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def resolutionArrow [Finite Λ] {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
        (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ⟶
      ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj I :=
  (NatTrans.mapHomologicalComplex (supportComparison Λ k r p i h).hom (.up ℤ)).app J ≫
  ((lowerStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).map t

/-- The chain transpose alpha followed by the ordinary r-counit and the chosen t.
Source: Stacks Tag 0F7B and the termwise adjunction
(blueprint: lem-cbc-etale-clopen-mate-normalization). -/
@[no_expose] def transposeArrow {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (J : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (I : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    (t : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) :
    ((upperStar (ModuleCat.{u + 1} Λ) p).mapHomologicalComplex (.up ℤ)).obj
        (((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapHomologicalComplex (.up ℤ)).obj
          (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J)) ⟶ I :=
  (NatTrans.mapHomologicalComplex (alpha Λ k r p i h) (.up ℤ)).app
    (((lowerStar (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex (.up ℤ)).obj J) ≫
  ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapHomologicalComplex (.up ℤ)).map
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r).mapHomologicalComplex
      (.up ℤ)).counit.app J) ≫ t

attribute [local irreducible] mate supportComparison normalizedComparison

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] derivedMate derivedAlpha alpha
  resolutionArrow transposeArrow

end ClopenMateNormalization
end AlgebraicGeometry.Etale
