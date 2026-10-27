/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.SpaceFppfHypercover
public import Sheaf.CategoryTheory.CochainCoefficientUniverseTransport
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Sheaf.AlgebraicGeometry.HypercoverAugmentationFaceProperty
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice
import Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence

/-! # Unbounded quasi-coherent descent on the face total site

Source: Stacks Project, spaces-simplicial.tex, Tags 0DHF and 0D7M,
with the injective-order-map total-site adaptation
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence).

The model records the actual enlarged sites, fibre-product functors, projection
comparisons and chart-normalized structural maps. Heterogeneous equalities only
transport these fixed data across the recorded fibre identifications. Rings use the
existing sectionwise ULift to the site universe. No model is chosen from a bare
existence assertion. The theorem supplies a model and applies to every such model.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open CategoryTheory.SemisimplicialRingedTotal

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The enlarged ringed site, with the existing explicit sectionwise coefficient lift.
Source: Stacks 03G0, 03G7, 03DA and 0DHF
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
def fppfFaceSite (X : AlgebraicSpace S) : Site.{u + 1} where
  C := X.EnlargedEtaleSite
  J := X.enlargedEtaleTopology
  ring := SheafOfModules.CochainUniverseTransport.ring.{u + 1, u + 1, u, u + 1, 0}
    X.enlargedCotangentStructure

/-- The degree space after discarding degeneracies.
Source: Stacks 0DHF, face-only adaptation
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
abbrev fppfFaceSpace {X : AlgebraicSpace S} (U : SimplicialObject (Over X))
    (i : SemiSimplexCategoryᵒᵖ) : AlgebraicSpace S :=
  (U.obj (op (SemiSimplexCategory.toSimplexCategory.obj i.unop))).left

/-- The structure map associated to an injective order map.
Source: Stacks 0DHF, face-only adaptation
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
abbrev fppfFaceMap {X : AlgebraicSpace S} (U : SimplicialObject (Over X))
    {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j) :
    fppfFaceSpace U i ⟶ fppfFaceSpace U j :=
  (U.map (SemiSimplexCategory.toSimplexCategory.map a.unop).op).left

/-- A presentation of precisely the enlarged étale face total site and augmentation.
All data are pinned to fibre products, projection comparisons and regular functions.
There is no descent or quasi-coherence hypothesis inside the model.
Source: Stacks 09WC, 09WF, 03G8, 0D70, 0DHF, face-only adaptation
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
structure FppfFaceTotalModel {X : AlgebraicSpace S} (U : SimplicialObject (Over X)) where
  diagram : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}
  fibre : ∀ i : SemiSimplexCategoryᵒᵖ,
    diagram.obj ⟨op i⟩ = Cat.of (fppfFaceSpace U i).EnlargedEtaleSite
  baseChange : ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
    HEq (diagram.map a.op.toLoc).toFunctor (enlargedBaseChange (fppfFaceMap U a))
  unitor : ∀ i : SemiSimplexCategoryᵒᵖ,
    HEq (Cat.Hom.toNatIso (diagram.mapId ⟨op i⟩))
      (enlargedIdentityIso (fppfFaceSpace U i))
  compositor : ∀ {i j k : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
    HEq (Cat.Hom.toNatIso (diagram.mapComp b.op.toLoc a.op.toLoc)).symm
      (enlargedCompositionIso (fppfFaceMap U a) (fppfFaceMap U b))
  sites : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ diagram
  covering : ∀ i : SemiSimplexCategoryᵒᵖ,
    HEq (sites.coverage i) (fppfFaceSpace U i).enlargedEtalePrecoverage
  rings : RingDiagram sites
  fibreRing : ∀ i : SemiSimplexCategoryᵒᵖ,
    HEq (rings.fibre i).ring (fppfFaceSite (fppfFaceSpace U i)).ring
  sheaf : Presheaf.IsSheaf sites.totalTopology rings.presheaf
  presentation : Presentation rings sheaf
  faceRing : ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
    HEq ((presentation.face a).adj.homEquiv _ _ (presentation.face a).ringMap)
      (chartNormalizedUnderlyingMap.{u, 0} (fppfFaceMap U a)
        (cotangentStructuralMap_existsUnique (fppfFaceMap U a)).choose)
  augmentation : Augmentation rings (fppfFaceSite X)
    presentation.face presentation.faceId presentation.faceComp
  augmentationDirect : ∀ i : SemiSimplexCategoryᵒᵖ,
    HEq (augmentation.map i).direct
      (enlargedDirectImage (U.obj (op
        (SemiSimplexCategory.toSimplexCategory.obj i.unop))).hom (Type (u + 1)))
  augmentationComparison : ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
    HEq ((conjugateIsoEquiv
      ((augmentation.map j).adj.comp (presentation.face a).adj)
      (augmentation.map i).adj) (augmentation.comparison a))
      (enlargedDirectCompositionIso (fppfFaceMap U a)
        (U.obj (op (SemiSimplexCategory.toSimplexCategory.obj j.unop))).hom
        (Type (u + 1)))
  augmentationRing : ∀ i : SemiSimplexCategoryᵒᵖ,
    HEq ((augmentation.map i).adj.homEquiv _ _ (augmentation.map i).ringMap)
      (chartNormalizedUnderlyingMap.{u, 0}
        (U.obj (op (SemiSimplexCategory.toSimplexCategory.obj i.unop))).hom
        (cotangentStructuralMap_existsUnique
          (U.obj (op (SemiSimplexCategory.toSimplexCategory.obj i.unop))).hom).choose)
  totalAugmentation : AugmentationPresentation presentation (fppfFaceSite X) augmentation

/-- Quasi-coherent total modules: componentwise quasi-coherent, with invertible transitions.
Source: Stacks 0D7M, face-only adaptation
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
def FppfFaceTotalModel.qcoh {X : AlgebraicSpace S} {U : SimplicialObject (Over X)}
    (M : FppfFaceTotalModel U) : ObjectProperty (M.rings.total M.sheaf).modules :=
  fun N ↦ (∀ i : SemiSimplexCategoryᵒᵖ,
    ((M.presentation.evaluation i).ordinary.obj N).IsQuasicoherent) ∧
    ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
      IsIso ((M.presentation.transition a).app N)

/-- The unbounded full subcategory with quasi-coherent cohomology systems.
Source: Stacks 0DHF (blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
def FppfFaceTotalModel.derivedQCoh {X : AlgebraicSpace S} {U : SimplicialObject (Over X)}
    (M : FppfFaceTotalModel U) : ObjectProperty (M.rings.total M.sheaf).D :=
  DerivedCategory.homologyProperty M.qcoh

/-- The cochain comparison of the specified right-derived pair, including both quotient
comparisons. Source: Stacks 070K, 0DHF
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence). -/
def fppfFaceRightComparison {T V : Site.{u + 1}} (G : T.modules ⥤ V.modules)
    [G.Additive] (RG : T.D ⥤ V.D)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG) (I : CochainComplex T.modules ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ⟶
      RG.obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso V.modules).app
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app I) ≫
    β.app ((HomotopyCategory.quotient T.modules (ComplexShape.up ℤ)).obj I) ≫
    RG.map ((DerivedCategory.quotientCompQhIso T.modules).hom.app I)

/-- Unbounded quasi-coherent descent, including the canonical derived adjunction.

Source: Stacks Project, spaces-simplicial.tex, Tags 0DHF and 0D7M;
sites-cohomology.tex, Tags 0D7V, 06YS and 06YY, with injective order maps only
(blueprint: lem-sfb-fppf-face-total-qcoh-equivalence).

Proof:
1. Use the enlarged-site model and its projection-normalized composition comparisons
   to form the coherent face diagram. Its ring is the extended structure sheaf.
   Apply lem-sfb-semisimplicial-ringed-total-category for its presentation and augmentation.
   The existing coefficient ULift preserves sections, tensors and all these comparisons.
2. By lem-sfb-hypercover-augmentation-face-property, all faces and augmentation maps
   are flat; hence their module pullbacks are exact. Evaluate a short exact sequence
   to prove exactness of total pullback. Exact jointly conservative evaluation and
   cohomology compatibility give precisely the cartesian criterion below.
3. Kernels and cokernels are componentwise quasi-coherent by
   lem-sfb-space-qcoh-kernels-colimits, and their transitions are invertible because
   face pullback is exact. For an extension, lem-sfb-space-qcoh-extension-closed
   supplies componentwise quasi-coherence and the short-five argument gives invertible
   transitions. Thus the total quasi-coherent modules form a weak Serre subcategory.
4. Apply lem-sfb-fppf-face-heart-descent and lem-sfb-fppf-face-heart-derived-unit:
   pullback is an equivalence on these hearts and its actual derived unit on every
   quasi-coherent module is invertible. No degeneracy needs to be flat.
5. Affine scheme objects form a basis of every enlarged site. Module categories are
   Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck, hence have enough injectives
   by lem-sp-grothendieck-enough-injectives. The exact free left adjoint of evaluation
   (lem-sfb-semisimplicial-evaluation-free-adjoint) makes evaluation preserve injectives.
   Thus cohomology at a total affine object is component cohomology at that object.
6. Use lem-pe-ringed-site-derived-evaluation-slice, the enlarged-site localization
   equivalence and lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence to
   identify this with cohomology on the affine scheme's own étale site. Pullback
   preserves quasi-coherence (lem-sfb-space-module-pullback-quasicoherent); use
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and
   lem-sc-etale-affine-qcoherent to get vanishing in positive degrees. The same argument
   works downstairs, on every affine refinement, with the common local bound zero.
7. Apply lem-sfb-ringed-unbounded-descent-criterion to the total augmentation and these
   two weak Serre categories. Steps 2--6 verify its exactness, heart, derived-heart-unit
   and both local-bound hypotheses. It gives preservation of quasi-coherent cohomology
   by both functors and the actual unit and counit isomorphisms, hence inverse
   equivalences on the full unbounded subcategories. They are triangulated since the
   ambient derived functors are triangulated and the cohomology subcategories are so.
8. K-injective resolutions exist by lem-sfb-grothendieck-k-injective; their universal
   right-derived pair computes direct image. By lem-pc-kflat-resolution and
   lem-weil-pbc-ringed-topoi-derived-pullback the specified left-derived functor is
   computed on flat-term K-flat resolutions. Derive the ordinary tensor/direct-image
   adjunction: its Hom formula on a flat K-flat complex and a K-injective complex is
   exactly the displayed normalization. This pins the adjunction and therefore its
   unit and counit. The argument never imposes boundedness, quasi-compactness or
   separatedness, and never invokes flatness of degeneracies. -/
theorem fppf_face_total_qcoh_equivalence {X : AlgebraicSpace S}
    (U : SimplicialObject (Over X)) (hU : IsSpaceFppfHypercover U) :
    Nonempty (FppfFaceTotalModel U) ∧
    ∀ M : FppfFaceTotalModel U,
      M.qcoh.IsClosedUnderKernels ∧ M.qcoh.IsClosedUnderCokernels ∧
      M.qcoh.IsClosedUnderExtensions ∧
      M.derivedQCoh.IsTriangulated ∧
      (DerivedCategory.homologyProperty
        (SheafOfModules.isQuasicoherent (fppfFaceSite X).rings)).IsTriangulated ∧
      (∀ B : (M.rings.total M.sheaf).D,
        M.derivedQCoh B ↔ M.presentation.IsCartesian B ∧
          ∀ i : SemiSimplexCategoryᵒᵖ,
            (DerivedCategory.homologyProperty
              (SheafOfModules.isQuasicoherent (M.rings.fibre i).rings))
                ((M.presentation.evaluation i).derived.obj B)) ∧
      (PreservesFiniteLimits M.totalAugmentation.pullback.ordinary ∧
        PreservesFiniteColimits M.totalAugmentation.pullback.ordinary) ∧
      ∃ (R : (M.rings.total M.sheaf).D ⥤ (fppfFaceSite X).D)
        (β : M.totalAugmentation.map.modules.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R),
        R.IsRightDerivedFunctor β
          (HomotopyCategory.quasiIso (M.rings.total M.sheaf).modules (ComplexShape.up ℤ)) ∧
        (∀ I : CochainComplex (M.rings.total M.sheaf).modules ℤ, I.IsKInjective →
          IsIso (fppfFaceRightComparison M.totalAugmentation.map.modules R β I)) ∧
        ∃ a : M.totalAugmentation.pullback.derived ⊣ R,
          (∀ (P : CochainComplex (fppfFaceSite X).modules ℤ)
            (I : CochainComplex (M.rings.total M.sheaf).modules ℤ),
            (fppfFaceSite X).flat P → I.IsKInjective →
            ∀ f : (M.totalAugmentation.pullback.ordinary.mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P ⟶ I,
              a.homEquiv _ _ (M.totalAugmentation.pullback.alpha P ≫ DerivedCategory.Q.map f) =
                DerivedCategory.Q.map
                  ((M.totalAugmentation.pullback.adjunction.mapHomologicalComplex
                    (ComplexShape.up ℤ)).homEquiv P I f) ≫
                  fppfFaceRightComparison M.totalAugmentation.map.modules R β I) ∧
          (∀ K : (fppfFaceSite X).D,
            DerivedCategory.homologyProperty
              (SheafOfModules.isQuasicoherent (fppfFaceSite X).rings) K →
            M.derivedQCoh (M.totalAugmentation.pullback.derived.obj K) ∧
              IsIso (a.unit.app K)) ∧
          (∀ B : (M.rings.total M.sheaf).D, M.derivedQCoh B →
            DerivedCategory.homologyProperty
              (SheafOfModules.isQuasicoherent (fppfFaceSite X).rings) (R.obj B) ∧
              IsIso (a.counit.app B)) ∧
          ∃ (_ : M.totalAugmentation.pullback.derived.CommShift ℤ) (_ : R.CommShift ℤ),
            M.totalAugmentation.pullback.derived.IsTriangulated ∧ R.IsTriangulated := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
