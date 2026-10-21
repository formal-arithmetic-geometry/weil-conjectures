/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.SectionDerivedTensorData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Sheaf.Algebra.Homology.KFlatModuleObject
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.ProjectionMateExact


public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Canonical derived section-module realization

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pd-section-derived-realization).

## Main definitions

- `derivedEquivalence`: localization of the fixed section equivalence.
- `derivedPullback`, `derivedPushforward`: actual ringed derived operations.
- `tensor`, `tensorComparison`, `qTensor`: the normalized K-flat tensor realization.
- `tensorPullComparison`: the uniquely specified ringed tensor-pullback map.
- `derivedExtension`, `derivedOpenAdjunction`: localized open extension and restriction.
- `derivedPullbackComposition`: localization of geometric pullback pasting.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ u₂ v₁ v₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The complete representative normalization, K-flat invertibility and regular-unit condition.
Source: Stacks 06YU and 07A4 (blueprint: def-pd-section-derived-realization). -/
def TensorRepresentativeCondition (X : Scheme.{u})
    (q : (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
        totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X)) : Prop :=
  (∀ P Q : CochainComplex (internalModules Λ X) ℤ,
        q.app
            ((((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj P),
              (((equivalence Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)) =
          (tensor Λ X).map (Prod.mkHom
            (sectionLocalizationComparison Λ X P).inv
            (sectionLocalizationComparison Λ X Q).inv) ≫
          (tensorComparison Λ X).inv.app ((DerivedCategory.Q (C := internalModules Λ X)).obj P,
            (DerivedCategory.Q (C := internalModules Λ X)).obj Q) ≫
          ((derivedEquivalence Λ X).functor).map (Functor.LaxMonoidal.μ
            (DerivedCategory.Q (C := internalModules Λ X)) P Q) ≫
          localizedTotalComparison Λ X P Q) ∧
      (∀ P Q : CochainComplex (modules Λ X) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients P ∨
          CochainComplex.IsKFlatIndependentCoefficients Q → IsIso (q.app (P, Q))) ∧
      Nonempty (tensorUnit Λ X ≅
        (DerivedCategory.singleFunctor (modules Λ X) 0).obj (𝟙_ (modules Λ X)))

/-- The transported tensor is the ringed-site K-flat derived tensor, including its unit.
Source: Stacks 06YU and 07A4
(blueprint: def-pd-section-derived-realization).
Proof: apply the existing normalized internal_section_tensor_comparison degreewise;
its summand equations identify the signed total tensors. Exactness preserves and
reflects acyclicity. Thus the two acyclic K-flat tests agree, using the signed
symmetry to interchange their test sides. On K-flat representatives the internal
localization tensor comparison is invertible. Transport it across the equivalence.
The local pure-tensor and regular-unit normalizations descend, so the unit is the
regular ring sheaf placed in degree zero. Every section-module complex is
isomorphic to a termwise image under E; naturality therefore uniquely determines
q on every pair of complexes. -/
theorem tensor_representatives (X : Scheme.{u}) :
    ∃! q : (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
        totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X),
      TensorRepresentativeCondition Λ X q := by
  sorry

/-- The actual internal derived tensor comparison, obtained by localizing its mate map.
Source: Stacks 07A4 (blueprint: def-pd-section-derived-realization). -/
def internalDelta {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.postcompose₂.obj (internalDerivedPullback Λ f)).obj (CondensedRing.derivedTensor Λ Y) ⟶
      (((Functor.whiskeringLeft₂ _).obj (internalDerivedPullback Λ f)).obj
        (internalDerivedPullback Λ f)).obj (CondensedRing.derivedTensor Λ X) :=
  (CondensedRing.upperStar Λ f).leftDerivedTensorComparison

/-- The derived pullback comparison, obtained by localizing the specified ordinary
comparison and the canonical exact-functor left-derived factorization.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-realization). -/
def derivedPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPullback Λ f) ⋙ (derivedEquivalence Λ X).functor ≅
      (derivedEquivalence Λ Y).functor ⋙ derivedPullback Λ f :=
  Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f)
      (derivedFunctor Λ X) ≪≫
    Functor.mapDerivedCategorySquareIso
      (F₁ := CondensedRing.upperStar Λ f) (F₂ := (equivalence Λ X).functor)
      (G₁ := (equivalence Λ Y).functor) (G₂ := pullback Λ f) (pullComparison Λ f)

/-- The derived pushforward comparison, via uniqueness of the K-injective right
 derived functors. Every factor is the specified resolution comparison.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-realization). -/
def derivedPushComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPushforward Λ f) ⋙ (derivedEquivalence Λ Y).functor ≅
      (derivedEquivalence Λ X).functor ⋙ derivedPushforward Λ f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (CondensedRing.lowerStar Λ f)
      (equivalence Λ Y).functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (pushComparison Λ f) ≪≫
    Functor.rightDerivedFunctorCompIso (equivalence Λ X).functor (pushforward Λ f) ≪≫
    Functor.isoWhiskerRight (equivalence Λ X).functor.rightDerivedFunctorIsoMapDerivedCategory
      (derivedPushforward Λ f)

/-- The canonical isomorphism from the conjugate internal pullback to ringed pullback.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-realization). -/
def conjugatePullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((derivedEquivalence Λ Y).inverse ⋙ (internalDerivedPullback Λ f)) ⋙
      (derivedEquivalence Λ X).functor ≅ derivedPullback Λ f :=
  Functor.associator (derivedEquivalence Λ Y).inverse (internalDerivedPullback Λ f)
      (derivedFunctor Λ X) ≪≫
    Functor.isoWhiskerLeft (derivedEquivalence Λ Y).inverse (derivedPullComparison Λ f) ≪≫
    (Functor.associator (derivedEquivalence Λ Y).inverse (derivedFunctor Λ Y)
      (derivedPullback Λ f)).symm ≪≫
    Functor.isoWhiskerRight (derivedEquivalence Λ Y).counitIso (derivedPullback Λ f) ≪≫
    Functor.leftUnitor (derivedPullback Λ f)

/-- The canonical isomorphism from the conjugate internal pushforward to ringed pushforward.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-realization). -/
def conjugatePushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedEquivalence Λ X).inverse ⋙
      ((internalDerivedPushforward Λ f) ⋙ (derivedEquivalence Λ Y).functor) ≅
        derivedPushforward Λ f :=
  Functor.isoWhiskerLeft (derivedEquivalence Λ X).inverse (derivedPushComparison Λ f) ≪≫
    (Functor.associator (derivedEquivalence Λ X).inverse (derivedFunctor Λ X)
      (derivedPushforward Λ f)).symm ≪≫
    Functor.isoWhiskerRight (derivedEquivalence Λ X).counitIso (derivedPushforward Λ f) ≪≫
    Functor.leftUnitor (derivedPushforward Λ f)

set_option linter.unusedSectionVars false in
/-- Exact sequential colimits transfer through the fixed section equivalence.
Source: Stacks 00YV (blueprint: def-pd-section-derived-realization).
Proof: transfer each diagram and its colimit along the exact equivalence. Its
inverse preserves finite limits, so the exactness of internal sequential colimits
implies exactness of the section-module colimits. -/
@[instance] theorem section_hasExactSequentialColimits (X : Scheme.{u}) :
    HasExactColimitsOfShape ℤ (modules Λ X) := by
  exact HasExactColimitsOfShape.of_codomain_equivalence ℤ (equivalence Λ X)

/-- The canonical derived adjunction of the ordinary ringed module adjunction.
Its left adjoint is expressed by exact localization using the canonical comparison.
Source: Stacks 07A6 (blueprint: def-pd-section-derived-realization). -/
def derivedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    derivedPullback Λ f ⊣ derivedPushforward Λ f :=
  ((adjunction Λ f).derivedAdjunction).ofNatIsoLeft
    ((pullback Λ f).leftDerivedFunctorIsoMapDerivedCategory)

/-- The localization tensor comparison selected by its complete normalization on
termwise equivalence images. Every complex is isomorphic to such an image, so
naturality and the displayed normalization determine this transformation uniquely.
Source: Stacks 06YU (blueprint: def-pd-section-derived-realization). -/
def qTensor (X : Scheme.{u}) :
    (((DerivedCategory.Q (C := modules Λ X)).prod
      (DerivedCategory.Q (C := modules Λ X))) ⋙ tensor Λ X) ⟶
      totalTensor Λ X ⋙ DerivedCategory.Q (C := modules Λ X) :=
  (tensor_representatives Λ X).exists.choose

/-- The signed total of the fixed ordinary oplax pullback tensor comparison.
Source: Stacks 07A4 (blueprint: def-pd-section-derived-realization). -/
def totalPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (modules Λ Y) ℤ) :
    ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((totalTensor Λ Y).obj (P, Q)) ⟶
      (totalTensor Λ X).obj
        (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
          ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) :=
  ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (eqToHom (totalTensor_obj Λ Y P Q)) ≫
    HomologicalComplex.mapBifunctorComparison
      (F := curriedTensor (modules Λ Y)) (F' := curriedTensor (modules Λ X))
      (G := pullback Λ f) (G₁ := pullback Λ f) (G₂ := pullback Λ f)
      (Functor.OplaxMonoidal.δNatTrans (pullback Λ f)) (ComplexShape.up ℤ) P Q ≫
    eqToHom (totalTensor_obj Λ X
      (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)).symm

/-- The specified tensor-pullback representative square, with the actual ordinary oplax mate.
Source: Stacks 07A4 (blueprint: def-pd-section-derived-realization). -/
def TensorPullRepresentativeCondition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : tensor Λ Y ⋙ derivedPullback Λ f ≅
        ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X) : Prop :=
  ∀ P Q : CochainComplex (modules Λ Y) ℤ,
        (derivedPullback Λ f).map ((qTensor Λ Y).app (P, Q)) ≫
            (pullback Λ f).mapDerivedCategoryFactors.hom.app ((totalTensor Λ Y).obj (P, Q)) ≫
            (DerivedCategory.Q (C := modules Λ X)).map (totalPullComparison Λ f P Q) =
          d.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
            (tensor Λ X).map (Prod.mkHom
              ((pullback Λ f).mapDerivedCategoryFactors.hom.app P)
              ((pullback Λ f).mapDerivedCategoryFactors.hom.app Q)) ≫
            (qTensor Λ X).app
              (((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
                ((pullback Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)

/-- The canonical ringed tensor-pullback map is uniquely specified on representatives.
Source: Stacks 07A4; ringedTopoiCanonicalDerivedTensorPullback
(blueprint: def-pd-section-derived-realization).
Proof: the normalized ordinary mate sends s tensor (m tensor n) to
(s tensor m) tensor (1 tensor n). The direct-sum total has those components
and the same signed differential. Compute on flat-term K-flat resolutions;
the qTensor maps are isomorphisms there. Two-variable localization gives the
natural isomorphism, and every pair has such resolutions, giving uniqueness.
Exactness of pullback and the localization factor maps extend the square to
all complex pairs, with no boundedness or flatness assumption on their terms. -/
theorem tensorPullComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : tensor Λ Y ⋙ derivedPullback Λ f ≅
        ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X,
      TensorPullRepresentativeCondition Λ f d := by
  sorry

/-- The canonical ringed tensor isomorphism selected by its unique representative square.
Source: Stacks 07A4 (blueprint: def-pd-section-derived-realization). -/
def tensorPullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor Λ Y ⋙ derivedPullback Λ f ≅
      ((derivedPullback Λ f).prod (derivedPullback Λ f)) ⋙ tensor Λ X :=
  (tensorPullComparison_existsUnique Λ f).exists.choose

/-- The existing levelwise comparison for extension by zero, fixed by its adjunction mate.
Source: Stacks 03DI (blueprint: def-pd-section-derived-realization). -/
def extensionComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek Λ j ⋙ (equivalence Λ X).functor ≅
      (equivalence Λ U).functor ⋙ extension Λ j :=
  ordinaryExtensionComparison Λ j

/-- The levelwise ringed extension on the unbounded derived category.
Source: Stacks 03DJ (blueprint: def-pd-section-derived-realization). -/
@[implicit_reducible]
def derivedExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    DerivedCategory (modules Λ U) ⥤ DerivedCategory (modules Λ X) :=
  (extension Λ j).mapDerivedCategory

/-- Localization of the specified levelwise extension comparison.
Source: Stacks 03DJ (blueprint: def-pd-section-derived-realization). -/
def derivedExtensionComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (internalDerivedExtension Λ j) ⋙
        (derivedEquivalence Λ X).functor ≅
      (derivedEquivalence Λ U).functor ⋙ derivedExtension Λ j :=
  Functor.mapDerivedCategorySquareIso
    (F₁ := CondensedRing.openImmersionLowerShriek Λ j) (F₂ := (equivalence Λ X).functor)
    (G₁ := (equivalence Λ U).functor) (G₂ := extension Λ j) (extensionComparison Λ j)

/-- The ringed open adjunction is the localization of the specified ordinary adjunction.
Source: Stacks 03DJ (blueprint: def-pd-section-derived-realization). -/
def derivedOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedExtension Λ j ⊣ derivedPullback Λ j :=
  (openAdjunction Λ j).mapDerivedCategoryAdjunction

/-- The actual internal open adjunction, with its right adjoint expressed as L j*.
Source: Stacks 03DJ (blueprint: def-pd-section-derived-realization). -/
def internalOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (internalDerivedExtension Λ j) ⊣
      (internalDerivedPullback Λ j) :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ j).symm

/-- Localization of the ringed pullback compositor specified by geometric pasting.
Source: Stacks 03D7 and 07A6
(blueprint: def-pd-section-derived-realization). -/
def derivedPullbackComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback Λ (f ≫ g) ≅ derivedPullback Λ g ⋙ derivedPullback Λ f :=
  Functor.mapDerivedCategoryNatIso (pullbackComposition Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso (pullback Λ g) (pullback Λ f)


end AlgebraicGeometry.ProEtale.ModuleRingedComparison
