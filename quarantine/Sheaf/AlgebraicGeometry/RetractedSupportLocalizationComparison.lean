/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
import Sheaf.AlgebraicGeometry.IntegralEtaleDirectImageExact
import Sheaf.AlgebraicGeometry.BoundedComplexDirectImagePresheaf
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
import Sheaf.AlgebraicGeometry.PurSupportExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# The localization triangle of a retracted closed section

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1, proof,
the first displayed localization triangle and its global boundary
(blueprint: lem-pur-retracted-support-localization-comparison).

The auxiliary definitions spell out the canonical comparison maps. In particular,
the first term uses the finite transported exceptional functor, not an assumed
exceptional adjunction on all pro-etale objects. Edge maps are characterized on
injective models by taking the local class of a global cocycle.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.ProEtale.RetractedSupport

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- The size convention for the existing coefficient module category.
Source: sk-prop-a1, finite coefficients
(blueprint: lem-pur-retracted-support-localization-comparison). -/
abbrev Modules := ModuleCat.{u + 1} P.Coefficient

/-- Ordinary module sheaves in the pro-etale topology.
Source: sk-prop-a1, localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
abbrev ProSheaves (T : Scheme.{u}) := Sheaf (Scheme.ProEt.topology T) (Modules P)

/-- Ordinary module sheaves in the etale topology.
Source: sk-prop-a1, etale origin of the localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
abbrev EtSheaves (T : Scheme.{u}) := Sheaf T.smallEtaleTopology (Modules P)

/-- Finiteness follows from the positive coefficient level in the conventions.
Source: sk-def-purity-conv; finite coefficient quotient
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable instance finiteRing : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- The standard universe lift preserves finiteness of the coefficient ring.
Source: sk-def-purity-conv, finite coefficients
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable instance finiteCoefficient : Finite P.Coefficient :=
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The bounded-below comparison inverse image, formed by the recorded exact functor.
Source: sk-prop-a1, finite etale/pro-etale transport
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev nuPlus (T : Scheme.{u}) :=
  (comparisonUpperStar (Modules P) T).mapDerivedCategoryPlus

/-- The same inverse image in the ordinary unbounded derived categories.
Source: sk-prop-a1, finite etale/pro-etale transport
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev nu (T : Scheme.{u}) :=
  (comparisonUpperStar (Modules P) T).mapDerivedCategory

/-- K = nu_X^* B, with its original bounded-below domain retained.
Source: sk-prop-a1, finite etale/pro-etale transport
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev input (X : Scheme.{u}) :=
  DerivedCategory.Plus.ι ⋙ nu P X

/-- The exceptional term uses exactly the identity/proper compactification of the section.
Source: sk-prop-a1, first term of the localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev closedTerm {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :=
  input P X ⋙ sfFiniteExceptionalFixed P.Ring (Compactification.ofIsProper s)

/-- The middle term is the ordinary total derived direct image.
Source: sk-prop-a1, middle term of the localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev middleTerm {X Y : Scheme.{u}} (p : X ⟶ Y) :=
  input P X ⋙ (lowerStar (Modules P) p).rightDerivedFunctor

/-- The open term uses pi = j followed by p, with exact open inverse image.
Source: sk-prop-a1, third term of the localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev openTerm {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ X) :=
  input P X ⋙ (upperStar (Modules P) j).mapDerivedCategory ⋙
    (lowerStar (Modules P) (j ≫ p)).rightDerivedFunctor

/-- The second arrow is restriction, followed by the recorded direct-image compositor.
Source: sk-prop-a1, second arrow of the localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def restriction {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ X) :
    middleTerm P p ⟶ openTerm P p j :=
  letI := (upperStarLowerStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  Functor.whiskerLeft (input P X)
    (Functor.whiskerRight
      (upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction.unit
      (lowerStar (Modules P) p).rightDerivedFunctor ≫
    Functor.whiskerLeft (upperStar (Modules P) j).mapDerivedCategory
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (Modules P) j) (lowerStar (Modules P) p)
        (lowerStarComp (Modules P) j p)).hom)

/-- The canonical derived direct-image comparison in unbounded coordinates, restricted
on inputs to D+. All factors are the published comparison mate and compatibility isos.
Source: sk-prop-a1, finite etale/pro-etale transport; Stacks Tag 099R
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def imageComparison {T V : Scheme.{u}} (f : T ⟶ V)
    (B : DerivedCategory.Plus (EtSheaves P T)) :
    (nu P V).obj ((Etale.lowerStar (Modules P) f).rightDerivedFunctor.obj B.obj) ⟶
      (lowerStar (Modules P) f).rightDerivedFunctor.obj ((input P T).obj B) :=
  (nu P V).map
      (((Etale.lowerStar (Modules P) f).rightDerivedFunctorPlusCompatibility.app B).inv) ≫
    ((comparisonUpperStar (Modules P) V).mapDerivedCategoryPlusCompatibility.app
      ((Etale.lowerStar (Modules P) f).rightDerivedFunctorPlus.obj B)).inv ≫
    DerivedCategory.Plus.ι.map ((comparisonDirectImageCanonicalMate P.Coefficient f).app B) ≫
    ((lowerStar (Modules P) f).rightDerivedFunctorPlusCompatibility.app
      ((nuPlus P T).obj B)).hom ≫
    (lowerStar (Modules P) f).rightDerivedFunctor.map
      (((comparisonUpperStar (Modules P) T).mapDerivedCategoryPlusCompatibility.app B).hom)

/-- The etale closed adjoint, before any constructible restriction.
Source: sk-prop-a1, ordinary closed-support localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev etClosed {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :=
  ((Etale.lowerStar (Modules P) s).rightDerivedFunctor).rightAdjoint

/-- Collapse Rp_* Rs_* to the identity along ps = id, using the canonical etale
compositor, equality transport, and identity-derived comparison.
Source: sk-prop-a1, apply Rp_* to localization
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def collapse {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) :
    (Etale.lowerStar (Modules P) s).rightDerivedFunctor ⋙
        (Etale.lowerStar (Modules P) p).rightDerivedFunctor ≅
      𝟭 (DerivedCategory (EtSheaves P Y)) :=
  Etale.rightDerivedLowerStarComp (Modules P) s p ≪≫
    Etale.rightDerivedLowerStarCongr (Modules P) hs ≪≫
    Functor.rightDerivedFunctorNatIso (Etale.lowerStarId (Modules P) Y) ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 (EtSheaves P Y)) ≪≫
    Functor.mapDerivedCategoryIdIso (EtSheaves P Y)

/-- The first comparison includes the counit-compatible uniqueness of the etale right
adjoint, and the unit B -> Rnu_* nu^* B. Thus it compares with the actual transported
exceptional functor at the specified identity/proper compactification.
Source: sk-prop-a1, identification of the supported first term
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def firstComparison {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X)
    [IsClosedImmersion s] (hs : s ≫ p = 𝟙 Y)
    (B : DerivedCategory.Plus (EtSheaves P X)) :
    (nu P Y).obj ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.obj
      ((Etale.lowerStar (Modules P) s).rightDerivedFunctor.obj
        ((etClosed P s).obj B.obj))) ⟶ (closedTerm P s).obj B :=
  letI := (Compactification.ofIsProper s).hasCompactification
  (nu P Y).map
    ((collapse P p s hs).hom.app ((etClosed P s).obj B.obj) ≫
      (Adjunction.rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint (Etale.lowerStar (Modules P) s).rightDerivedFunctor)
        ((Etale.rightDerivedUpperShriekAdjunction (Modules P) s).ofNatIsoLeft
          (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (Modules P) s))).hom.app
            B.obj ≫
      (Etale.rightDerivedUpperShriek (Modules P) s).map
        ((comparisonAdjunction (Modules P) X).mapDerivedCategoryRightDerivedAdjunction.unit.app
          B.obj))

/-- Canonical comparison for the third term, including the open pullback comparison.
Source: sk-prop-a1, comparison of localization triangles
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def thirdComparison {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ X)
    (B : DerivedCategory.Plus (EtSheaves P X)) :
    (nu P Y).obj ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.obj
      ((Etale.lowerStar (Modules P) j).rightDerivedFunctor.obj
        ((Etale.upperStar (Modules P) j).mapDerivedCategory.obj B.obj))) ⟶
      (openTerm P p j).obj B :=
  (nu P Y).map ((Etale.rightDerivedLowerStarComp (Modules P) j p).hom.app _) ≫
    (nu P Y).map ((Etale.lowerStar (Modules P) (j ≫ p)).rightDerivedFunctor.map
      (((Etale.upperStar (Modules P) j).mapDerivedCategoryPlusCompatibility.app B).inv)) ≫
    imageComparison P (j ≫ p) ((Etale.upperStar (Modules P) j).mapDerivedCategoryPlus.obj B) ≫
    (lowerStar (Modules P) (j ≫ p)).rightDerivedFunctor.map
      ((nu P U).map
        (((Etale.upperStar (Modules P) j).mapDerivedCategoryPlusCompatibility.app B).hom) ≫
      (sfDerivedComparisonPullbackIso P.Ring j).inv.app B.obj)

/-- The global derived sections functor, using the ordinary K-injective derivation.
Source: sk-prop-a1, global supported cohomology
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev global (T : Scheme.{u}) :=
  (globalSectionsFunctor (Modules P) T).rightDerivedFunctor

/-- Integer-indexed global hypercohomology, retaining the module structure.
Source: sk-prop-a1, global boundary
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev hyper (T : Scheme.{u}) (q : ℤ) :=
  global P T ⋙ DerivedCategory.homologyFunctor (Modules P) q

/-- Global sections of the cohomology sheaf.
Source: sk-prop-a1, local classes and the edge map
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable abbrev localClasses (T : Scheme.{u}) (q : ℤ) :=
  DerivedCategory.homologyFunctor (ProSheaves P T) q ⋙ globalSectionsFunctor (Modules P) T

/-- The specified local-class normalization of an edge map. The equality is on cycles
of sections of every K-injective representative: take the sheaf cohomology class of that
same cocycle. It determines the edge map, including on arbitrary shifts.
Source: sk-prop-a1, edge compatibility; Stacks Tag 09A6
(blueprint: lem-pur-retracted-support-localization-comparison). -/
def EdgeNormalization (T : Scheme.{u}) (q : ℤ)
    (e : hyper P T q ⟶ localClasses P T q) : Prop :=
  ∀ (I : CochainComplex (ProSheaves P T) ℤ) [I.IsKInjective],
    (((globalSectionsFunctor (Modules P) T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ q ≫
      (DerivedCategory.homologyFunctorFactors (Modules P) q).inv.app _ ≫
      (DerivedCategory.homologyFunctor (Modules P) q).map
        ((globalSectionsFunctor (Modules P) T).rightDerivedFunctorObjQIso I).inv ≫
      e.app (DerivedCategory.Q.obj I) =
    ((((I.sc q).map (globalSectionsFunctor (Modules P) T)).cyclesIsoKernel) ≪≫
      (asIso (kernelComparison (I.sc q).g (globalSectionsFunctor (Modules P) T))).symm ≪≫
      (globalSectionsFunctor (Modules P) T).mapIso (I.sc q).cyclesIsoKernel.symm).hom ≫
      (globalSectionsFunctor (Modules P) T).map (I.homologyπ q) ≫
      (globalSectionsFunctor (Modules P) T).map
        ((DerivedCategory.homologyFunctorFactors (ProSheaves P T) q).inv.app I)

end AlgebraicGeometry.ProEtale.RetractedSupport

namespace AlgebraicGeometry.ProEtale.RetractedSupport

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Evaluation of direct image at the terminal object, using the canonical pullback
projection X times_Y Y -> X. This avoids choosing any global-sections isomorphism.
Source: sk-prop-a1, global comparison; Stacks Tag 0D6H
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def imageSectionsIso {T V : Scheme.{u}} (f : T ⟶ V) :
    lowerStar (Modules P) f ⋙ globalSectionsFunctor (Modules P) V ≅
      globalSectionsFunctor (Modules P) T :=
  ((sheafSections (Scheme.ProEt.topology T) (Modules P)).mapIso
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 V) f))
      (Category.comp_id _)).op).symm

/-- The Leray identification of derived global sections is the derived terminal-evaluation
identification, with the canonical K-injective composition comparison.
Source: sk-prop-a1, global comparison; Stacks Tag 0D6H
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def imageGlobalIso {T V : Scheme.{u}} (f : T ⟶ V) :
    (lowerStar (Modules P) f).rightDerivedFunctor ⋙ global P V ≅ global P T :=
  letI := (upperStarLowerStarAdjunction (Modules P) f).preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso' _ _ (imageSectionsIso P f)

/-- Open global sections are evaluation on that open object of the original site.
The isomorphism is the published restriction-to-localization comparison.
Source: sk-prop-a1, global restriction; Stacks Tag 08FI
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def openSectionsIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    upperStar (Modules P) j ⋙ globalSectionsFunctor (Modules P) U ≅
      sectionsFunctor (Modules P) (Scheme.ProEt.mk j) :=
  Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction (Modules P) j inferInstance)
      (globalSectionsFunctor (Modules P) U) ≪≫
    (proEtaleLocalizationSectionsIso (Scheme.ProEt.mk j) P.Coefficient).symm

/-- The canonical bounded/unbounded coordinate comparison for a section functor.
Source: sk-prop-a1, global sections; Stacks Tag 070I
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def sectionPlusIso (X : Scheme.{u}) (W : X.ProEt) (q : ℤ) :
    DerivedCategory.Plus.ι ⋙ (sectionsFunctor (Modules P) W).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor (Modules P) q ≅
      Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology X) (Modules P) W q :=
  Functor.isoWhiskerRight (sectionsFunctor (Modules P) W).rightDerivedFunctorPlusCompatibility.symm
    (DerivedCategory.homologyFunctor (Modules P) q)

/-- The canonical identification H(Y,Rp_*K) = H(X,K).
Source: sk-prop-a1, apply global sections; Stacks Tag 0D6H
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def middleGlobalIso {X Y : Scheme.{u}} (p : X ⟶ Y) (q : ℤ) :
    middleTerm P p ⋙ hyper P Y q ≅
      nuPlus P X ⋙ Sheaf.sectionHypercohomologyFunctor
        (Scheme.ProEt.topology X) (Modules P) (Scheme.ProEt.mk (𝟙 X)) q :=
  Functor.isoWhiskerLeft (input P X)
      (Functor.isoWhiskerRight (imageGlobalIso P p)
        (DerivedCategory.homologyFunctor (Modules P) q)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (comparisonUpperStar (Modules P) X).mapDerivedCategoryPlusCompatibility.symm
        (global P X)) (DerivedCategory.homologyFunctor (Modules P) q) ≪≫
    Functor.isoWhiskerLeft (nuPlus P X) (sectionPlusIso P X (Scheme.ProEt.mk (𝟙 X)) q)

/-- The canonical identification H(Y,Rpi_*j^*K) = H(U,j^*K), with evaluation on U
in the original site. All factors are normalized by the original section maps.
Source: sk-prop-a1, open global term; Stacks Tags 0D6H and 08FI
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def openGlobalIso {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ X)
    [IsOpenImmersion j] (q : ℤ) :
    openTerm P p j ⋙ hyper P Y q ≅
      nuPlus P X ⋙ Sheaf.sectionHypercohomologyFunctor
        (Scheme.ProEt.topology X) (Modules P) (Scheme.ProEt.mk j) q :=
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  Functor.isoWhiskerLeft (input P X ⋙ (upperStar (Modules P) j).mapDerivedCategory)
      (Functor.isoWhiskerRight (imageGlobalIso P (j ≫ p))
        (DerivedCategory.homologyFunctor (Modules P) q)) ≪≫
    Functor.isoWhiskerLeft (input P X)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight
          (Functor.rightDerivedFunctorIsoMapDerivedCategory
            (upperStar (Modules P) j)).symm (global P U) ≪≫
          Functor.rightDerivedFunctorCompIso' _ _ (openSectionsIso P j))
        (DerivedCategory.homologyFunctor (Modules P) q)) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        (comparisonUpperStar (Modules P) X).mapDerivedCategoryPlusCompatibility.symm
        (sectionsFunctor (Modules P) (Scheme.ProEt.mk j)).rightDerivedFunctor)
      (DerivedCategory.homologyFunctor (Modules P) q) ≪≫
    Functor.isoWhiskerLeft (nuPlus P X) (sectionPlusIso P X (Scheme.ProEt.mk j) q)

/-- The ordinary etale boundary has the exact source and target of the recorded
closed adjunction and open adjunction. Naturality is encoded as a natural transformation.
Source: sk-prop-a1, etale localization triangle
(blueprint: lem-pur-retracted-support-localization-comparison). -/
abbrev EtaleBoundary {X Y U : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] (j : U ⟶ X) :=
  (Etale.upperStar (Modules P) j).mapDerivedCategory ⋙
      (Etale.lowerStar (Modules P) j).rightDerivedFunctor ⟶
    (etClosed P s ⋙ (Etale.lowerStar (Modules P) s).rightDerivedFunctor) ⋙
      shiftFunctor (DerivedCategory (EtSheaves P X)) (1 : ℤ)

/-- The etale triangle with the recorded closed counit and open unit.
Source: sk-prop-a1, localization before applying Rp_*
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def etaleTriangle {X Y U : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) (δ : EtaleBoundary P s j) (B : DerivedCategory (EtSheaves P X)) :
    Triangle (DerivedCategory (EtSheaves P X)) :=
  Triangle.mk
    ((Adjunction.ofIsLeftAdjoint (Etale.lowerStar (Modules P) s).rightDerivedFunctor).counit.app B)
    ((Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j).unit.app B) (δ.app B)

/-- Transport the entire etale triangle, retaining its third arrow and the functors'
shift comparisons. This fixes the sign of the transported boundary.
Source: sk-prop-a1, apply Rp_* then nu_Y^*
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def transportedTriangle {X Y U : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X)
    [IsClosedImmersion s] (j : U ⟶ X) (δ : EtaleBoundary P s j)
    (B : DerivedCategory.Plus (EtSheaves P X)) :
    Triangle (DerivedCategory (ProSheaves P Y)) :=
  (nu P Y).mapTriangle.obj
    ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.mapTriangle.obj
      (etaleTriangle P s j δ B.obj))

/-- The global boundary of a derived triangle, with the standard shift convention.
Source: sk-prop-a1, global support boundary
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def globalBoundary (Y : Scheme.{u})
    (T : Triangle (DerivedCategory (ProSheaves P Y))) (q : ℤ) :
    (hyper P Y q).obj T.obj₃ ⟶ (hyper P Y (q + 1)).obj T.obj₁ :=
  DerivedCategory.HomologySequence.δ ((global P Y).mapTriangle.obj T) q (q + 1) rfl

/-- The support boundary is normalized by the actual snake boundary on each bounded
below injective model. In particular, replacing it by its negative is not allowed.
Source: sk-prop-a1, global support boundary; Stacks Tags 09XP and 0117
(blueprint: lem-pur-retracted-support-localization-comparison). -/
def SupportBoundaryNormalization {Z X : Scheme.{u}} (s : Z ⟶ X) [IsClosedImmersion s]
    (δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X) (Modules P)
      (supportRestrictionArrow s) ⊤) : Prop :=
  ∀ (I : CochainComplex.Plus (ProSheaves P X)) [∀ r : ℤ, Injective (I.obj.X r)],
    ∃ (w : (NatTrans.mapHomologicalComplex
          (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
            (supportRestrictionArrow s)) (ComplexShape.up ℤ)).app I.obj ≫
        (NatTrans.mapHomologicalComplex
          ((sheafSections (Scheme.ProEt.topology X) (Modules P)).map
            (supportRestrictionArrow s).op) (ComplexShape.up ℤ)).app I.obj = 0)
      (hS : (ShortComplex.mk _ _ w).ShortExact),
      ∀ q : ℤ,
        Sheaf.supportSequenceModelBoundary (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s) ⊤ δ I
          ⟨DerivedCategory.Plus.Q.obj I, trivial⟩ (Iso.refl _) q = hS.δ q (q + 1) rfl

end AlgebraicGeometry.ProEtale.RetractedSupport

namespace AlgebraicGeometry.ProEtale.RetractedSupport

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Identify the chosen complementary open with the canonical support open, at the level
of derived evaluation. The iso is contravariant because sections are contravariant.
Source: sk-prop-a1, support term and its open complement
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def complementSectionsIso {X Y U : Scheme.{u}} (s : Y ⟶ X)
    [IsClosedImmersion s] (j : U ⟶ X) [IsOpenImmersion j]
    (eU : Scheme.ProEt.mk j ≅ Scheme.ProEt.mk s.openComplement.ι) (q : ℤ) :
    Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology X) (Modules P)
        (Scheme.ProEt.mk j) q ≅
      Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology X) (Modules P)
        (Scheme.ProEt.mk s.openComplement.ι) q :=
  Functor.isoWhiskerRight
    (Functor.rightDerivedFunctorPlusNatIso
      (F := sectionsFunctor (Modules P) (Scheme.ProEt.mk j))
      (G := sectionsFunctor (Modules P) (Scheme.ProEt.mk s.openComplement.ι))
      ((sheafSections (Scheme.ProEt.topology X) (Modules P)).mapIso eU.op).symm)
    (DerivedCategory.Plus.homologyFunctor (Modules P) q)

/-- The canonical global etale/pro-etale comparison is induced by the comparison unit,
followed by the derived identity nu_* followed by etale sections = pro-etale sections.
Source: sk-prop-a1, comparison on global cohomology; Stacks Tag 099R
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def etaleGlobalComparison (T : Scheme.{u}) :
    (Etale.sectionsFunctor (Modules P) T).rightDerivedFunctor ⟶
      nu P T ⋙ global P T :=
  letI := (comparisonAdjunction (Modules P) T).preservesKInjectiveComplexes
  Functor.whiskerRight
      (comparisonAdjunction (Modules P) T).mapDerivedCategoryRightDerivedAdjunction.unit
      (Etale.sectionsFunctor (Modules P) T).rightDerivedFunctor ≫
    Functor.whiskerLeft (nu P T)
      (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).hom

/-- The canonical map on global sections of cohomology sheaves: the sheaf comparison
unit, then exact inverse image commuting with cohomology.
Source: sk-prop-a1, comparison of local classes
(blueprint: lem-pur-retracted-support-localization-comparison). -/
noncomputable def etaleLocalComparison (T : Scheme.{u}) (q : ℤ)
    (B : DerivedCategory (EtSheaves P T)) :
    (Etale.sectionsFunctor (Modules P) T).obj
        ((DerivedCategory.homologyFunctor (EtSheaves P T) q).obj B) ⟶
      (localClasses P T q).obj ((nu P T).obj B) :=
  (Etale.sectionsFunctor (Modules P) T).map
      ((comparisonAdjunction (Modules P) T).unit.app
        ((DerivedCategory.homologyFunctor (EtSheaves P T) q).obj B)) ≫
    (globalSectionsFunctor (Modules P) T).map
      (((comparisonUpperStar (Modules P) T).mapDerivedCategoryHomologyFunctorIso q).hom.app B)

/-- The etale version of the same cocycle normalization, written out so the comparison
assertion is about the canonical edge maps, rather than arbitrary natural maps.
Source: sk-prop-a1, comparison with ordinary etale counterparts
(blueprint: lem-pur-retracted-support-localization-comparison). -/
def EtaleEdgeNormalization (T : Scheme.{u}) (q : ℤ)
    (e : (Etale.sectionsFunctor (Modules P) T).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor (Modules P) q ⟶
      DerivedCategory.homologyFunctor (EtSheaves P T) q ⋙
        Etale.sectionsFunctor (Modules P) T) : Prop :=
  ∀ (I : CochainComplex (EtSheaves P T) ℤ) [I.IsKInjective],
    (((Etale.sectionsFunctor (Modules P) T).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ q ≫
      (DerivedCategory.homologyFunctorFactors (Modules P) q).inv.app _ ≫
      (DerivedCategory.homologyFunctor (Modules P) q).map
        ((Etale.sectionsFunctor (Modules P) T).rightDerivedFunctorObjQIso I).inv ≫
      e.app (DerivedCategory.Q.obj I) =
    ((((I.sc q).map (Etale.sectionsFunctor (Modules P) T)).cyclesIsoKernel) ≪≫
      (asIso (kernelComparison (I.sc q).g (Etale.sectionsFunctor (Modules P) T))).symm ≪≫
      (Etale.sectionsFunctor (Modules P) T).mapIso (I.sc q).cyclesIsoKernel.symm).hom ≫
      (Etale.sectionsFunctor (Modules P) T).map (I.homologyπ q) ≫
      (Etale.sectionsFunctor (Modules P) T).map
        ((DerivedCategory.homologyFunctorFactors (EtSheaves P T) q).inv.app I)

/-- The complete comparison assertion, packaged only to keep the theorem signature
readable. The maps are fixed by etale counits, units, the comparison mate, and the
snake-boundary normalization. Every cohomology degree is an integer.
Source: sk-prop-a1, localization and its global support boundary
(blueprint: lem-pur-retracted-support-localization-comparison). -/
structure Comparison {X Y U : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X)
    [IsClosedImmersion s] (j : U ⟶ X) [IsOpenImmersion j] (hs : s ≫ p = 𝟙 Y) where
  /-- The first arrow; its etale counit normalization is in `transport`. -/
  first : closedTerm P s ⟶ middleTerm P p
  /-- The natural boundary of the displayed triangle. -/
  boundary : openTerm P p j ⟶ closedTerm P s ⋙
    shiftFunctor (DerivedCategory (ProSheaves P Y)) (1 : ℤ)
  /-- The original natural etale boundary. -/
  etaleBoundary : EtaleBoundary P s j
  /-- The ordinary etale localization triangle is distinguished. -/
  etale_distinguished : ∀ B : DerivedCategory (EtSheaves P X),
    etaleTriangle P s j etaleBoundary B ∈ distTriang _
  /-- No bounded constructibility condition is imposed on the input B. -/
  bounded_closed : ∀ B : DerivedCategory.Plus (EtSheaves P X),
    ∃ r : ℤ, DerivedCategory.IsGE ((closedTerm P s).obj B) r
  /-- The exact triangle in the question, with its restriction arrow. -/
  distinguished : ∀ B : DerivedCategory.Plus (EtSheaves P X),
    Triangle.mk (first.app B) ((restriction P p j).app B) (boundary.app B) ∈ distTriang _
  /-- All three comparison maps are the canonical specified ones. The third commutative
  square in this triangle isomorphism includes the boundary and its sign. -/
  transport : ∀ B : DerivedCategory.Plus (EtSheaves P X),
    ∃ e : transportedTriangle P p s j etaleBoundary B ≅
        Triangle.mk (first.app B) ((restriction P p j).app B) (boundary.app B),
      e.hom.hom₁ = firstComparison P p s hs B ∧
      e.hom.hom₂ = imageComparison P p B ∧ e.hom.hom₃ = thirdComparison P p j B
  /-- Any specified complement is canonically the support open. -/
  complement : Scheme.ProEt.mk j ≅ Scheme.ProEt.mk s.openComplement.ι
  /-- Supported hypercohomology is the ordinary kernel-derived functor from the
  recorded definition, naturally in B. -/
  supportIso : ∀ q : ℤ, closedTerm P s ⋙ hyper P Y q ≅
    nuPlus P X ⋙ Sheaf.supportHypercohomologyFunctor
      (Scheme.ProEt.topology X) (Modules P) (supportRestrictionArrow s) q
  /-- The global support boundary from the recorded long exact sequence. -/
  supportBoundary : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X) (Modules P)
    (supportRestrictionArrow s) ⊤
  /-- All three positions of the support long exact sequence are exact. -/
  support_exact : Sheaf.SupportSequenceExact (Scheme.ProEt.topology X) (Modules P)
    (supportRestrictionArrow s) ⊤ supportBoundary
  /-- The boundary has the injective-model snake normalization. -/
  support_normalized : SupportBoundaryNormalization P s supportBoundary
  /-- The first global arrow is the actual supported-section inclusion. -/
  global_first : ∀ (B : DerivedCategory.Plus (EtSheaves P X)) (q : ℤ),
    (hyper P Y q).map (first.app B) ≫ (middleGlobalIso P p q).hom.app B =
      (supportIso q).hom.app B ≫
        (Sheaf.supportHypercohomologyInclusion (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s) q).app ((nuPlus P X).obj B)
  /-- The global third arrow is precisely the support boundary, with no extra sign. -/
  global_boundary : ∀ (B : DerivedCategory.Plus (EtSheaves P X)) (q : ℤ),
    globalBoundary P Y
        (Triangle.mk (first.app B) ((restriction P p j).app B) (boundary.app B)) q ≫
        (supportIso (q + 1)).hom.app B =
      (openGlobalIso P p j q).hom.app B ≫
        (complementSectionsIso P s j complement q).hom.app ((nuPlus P X).obj B) ≫
        (supportBoundary q).app ⟨(nuPlus P X).obj B, trivial⟩
  /-- The canonical edge map from global classes to their local cohomology classes. -/
  edge : ∀ q : ℤ, hyper P Y q ⟶ localClasses P Y q
  /-- Its value on every injective representative is specified. -/
  edge_normalized : ∀ q : ℤ, EdgeNormalization P Y q (edge q)
  /-- The edge formula as equality of module maps, hence for every alpha. -/
  edge_boundary : ∀ (B : DerivedCategory.Plus (EtSheaves P X)) (q : ℤ),
    globalBoundary P Y
        (Triangle.mk (first.app B) ((restriction P p j).app B) (boundary.app B)) q ≫
        (edge (q + 1)).app ((closedTerm P s).obj B) =
      (edge q).app ((openTerm P p j).obj B) ≫
        (globalSectionsFunctor (Modules P) Y).map
          (DerivedCategory.HomologySequence.δ
            (Triangle.mk (first.app B) ((restriction P p j).app B) (boundary.app B))
            q (q + 1) rfl)
  /-- The corresponding ordinary etale edge map. -/
  etaleEdge : ∀ q : ℤ,
    (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor (Modules P) q ⟶
      DerivedCategory.homologyFunctor (EtSheaves P Y) q ⋙ Etale.sectionsFunctor (Modules P) Y
  /-- The same local-cocycle normalization on the etale site. -/
  etale_edge_normalized : ∀ q : ℤ, EtaleEdgeNormalization P Y q (etaleEdge q)
  /-- Global site comparison is invertible on every bounded-below etale input. -/
  global_comparison_iso : ∀ B : DerivedCategory.Plus (EtSheaves P Y),
    IsIso ((etaleGlobalComparison P Y).app B.obj)
  /-- Edge maps commute with the canonical global and cohomology-sheaf comparisons.
  Naturality of these comparisons also transports every arrow of `transport`, and
  therefore the support boundary and identifications, to their etale counterparts. -/
  edge_comparison : ∀ (B : DerivedCategory.Plus (EtSheaves P Y)) (q : ℤ),
    (DerivedCategory.homologyFunctor (Modules P) q).map
        ((etaleGlobalComparison P Y).app B.obj) ≫
        (edge q).app ((nu P Y).obj B.obj) =
      (etaleEdge q).app B.obj ≫ etaleLocalComparison P Y q B.obj

/-- A retracted closed section has the natural distinguished localization triangle,
its canonical etale/pro-etale comparison, the global supported-cohomology identification,
and the displayed compatibility of the boundary with canonical local-class edge maps.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1/sk-prop-a1.proof.md,
first displayed triangle and following global paragraph; Stacks Tags 09XP, 09XQ, 0D6H,
0D6E, 09A6 and 099R
(blueprint: lem-pur-retracted-support-localization-comparison).

Proof, following the twelve steps of the node:
1. A closed section is proper. Use its identity/proper compactification. Exactness of
etale closed direct image identifies compact support with direct image on K-injective
representatives; uniqueness of right adjoints identifies their counits. The derived
comparison unit on bounded-below etale B identifies the finite exceptional term with
nu_Y^* s^times B, naturally in B (sk-prop-sf-comparison).
2. Apply Rp_et,* to lem-exc-closed-support-triangle. It is triangulated, and the
canonical composition and identity isomorphisms collapse Rp_*s_* by ps = id.
3. Apply exact nu_Y^*. Use sk-thm-pe-direct-image-comparison for p, j, pi and s.
The canonical mate respects the open unit and closed counit. Transport the whole
triangle, including the shift comparison, to fix the third arrow and its sign.
4. Compare with lem-pur-support-localization-triangle. TR3 extends the identities of
the middle and open terms, and the two-out-of-three theorem makes the first map invertible.
5. Exact full faithfulness of s_* identifies this first map with the unique transpose
of the transported counit under the support adjunction. It is natural and independent
of the TR3 completion, and identifies the entire supported triangle.
6. The sheaf functor s^!_0 = s^* G_Z is right adjoint to exact s_*. Hence it preserves
injectives. On a bounded-below injective representative I it computes the support
exceptional object and its derived global sections.
7. The sectionwise support-kernel formula identifies Gamma(Y,s^!_0 I) with
ker(I(X) -> I(U)), degree by degree and with their differentials. This gives supportIso.
8. Injectivity makes restriction I^r(X) -> I^r(U) surjective, using the mono
j_! A_U -> A_X. Its kernel is the supported sections. The cone-to-quotient map q
and negative shifted projection -p give the boundary: a lift b of a cocycle c
has cone cocycle (b,-db), whose image under -p is db. This is the snake boundary,
with no additional sign (thm-pur-with-support-exactness).
9. Direct images preserve K-injectives as right adjoints to exact pullback. Their
global derived sections are evaluation at the final object. The resulting canonical
Leray comparisons give middleGlobalIso and openGlobalIso and identify the global boundary.
10. For the identity morphism the bounded-complex cohomology-presheaf comparison
identifies the cohomology sheaf with the sheafification of local hypercohomology.
Sending a global cocycle to its local class gives EdgeNormalization. Chain-map
representatives give naturality; homotopies act identically. It commutes with shifts,
since negating the differentials changes neither cycles nor boundaries.
11. Apply this naturality to the third arrow with target C[1]. Shift compatibility
and step 9 give edge_boundary in every integer degree, equivalently the formula for alpha.
12. By construction transport is the canonical etale/pro-etale comparison of all
three arrows. The comparison unit gives the natural global comparison, compatible
with shifts. Restricting a class to each etale test object commutes with the unit;
sheafification gives edge_comparison. Hence the global identifications, boundary,
and edge formula agree with their ordinary etale counterparts. -/
theorem exists_comparison
    {X Y U : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of P.field.k))]
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (s : Y ⟶ X) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 Y)
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcompl : IsCompl (Set.range s.base) (Set.range j.base)) :
    Nonempty (Comparison P p s j hs) := by
  sorry

end AlgebraicGeometry.ProEtale.RetractedSupport
