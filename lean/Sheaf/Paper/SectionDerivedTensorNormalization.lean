/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module
public import Sheaf.Paper.SectionDerivedPushpullNormalization
public import Sheaf.Paper.SectionOrdinaryOplaxNormalization
public import Mathlib.CategoryTheory.Monoidal.Transport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.InternalSectionTensorComparison
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.Algebra.Homology.KFlatModuleObject
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.DerivedPullbackRepresentativeComputation
import Sheaf.Paper.TensorPullbackRepresentativeDescent

/-! # Derived tensor normalization under the section equivalence

Source: Stacks Project, Cohomology on Sites, Tag 07A4,
`lemma-pullback-tensor-product`; Tags 06YU and 0G7E; Modules on Sites, Tag 03EL
(blueprint: lem-pd-section-derived-tensor-normalization).

The statement compares the specified localization, tensor, unit and pullback maps.
Its helper definitions expose existing transported constraints and the localized
scalar-multiplication unit. All complexes and derived inputs are unbounded.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.all false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
/-- Associator and unitor compatibility for a specified tensor comparison.
Source: Stacks 06YU and 07A4 (blueprint: lem-pd-section-derived-tensor-normalization). -/
def TensorConstraintCondition
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (B : C × C ⥤ C) (T : D × D ⥤ D) (I : C) (J : D)
    (a : ∀ M N P : C, B.obj (B.obj (M, N), P) ≅ B.obj (M, B.obj (N, P)))
    (l : ∀ M : C, B.obj (I, M) ≅ M) (r : ∀ M : C, B.obj (M, I) ≅ M)
    (a' : ∀ M N P : D, T.obj (T.obj (M, N), P) ≅ T.obj (M, T.obj (N, P)))
    (l' : ∀ M : D, T.obj (J, M) ≅ M) (r' : ∀ M : D, T.obj (M, J) ≅ M)
    (d : B ⋙ F ⟶ (F.prod F) ⋙ T) (e : F.obj I ⟶ J) : Prop :=
  (∀ M N P : C,
    F.map (a M N P).hom ≫ d.app (M, B.obj (N, P)) ≫
        T.map (Prod.mkHom (𝟙 (F.obj M)) (d.app (N, P))) =
      d.app (B.obj (M, N), P) ≫ T.map (Prod.mkHom (d.app (M, N)) (𝟙 (F.obj P))) ≫
        (a' (F.obj M) (F.obj N) (F.obj P)).hom) ∧
  (∀ M : C, d.app (I, M) ≫ T.map (Prod.mkHom e (𝟙 (F.obj M))) ≫
      (l' (F.obj M)).hom = F.map (l M).hom) ∧
  (∀ M : C, d.app (M, I) ≫ T.map (Prod.mkHom (𝟙 (F.obj M)) e) ≫
      (r' (F.obj M)).hom = F.map (r M).hom)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]
/-- The associator of the existing conjugate tensor, with the equivalence fixed.
Source: Stacks 06YU (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedAssociator (T : Scheme.{u})
    (M N P : DerivedCategory (modules Λ T)) :
    (tensor Λ T).obj ((tensor Λ T).obj (M, N), P) ≅
      (tensor Λ T).obj (M, (tensor Λ T).obj (N, P)) :=
  @MonoidalCategoryStruct.associator _ _
    (Monoidal.transportStruct (derivedEquivalence Λ T)) M N P


/-- The left unitor of the existing conjugate tensor.
Source: Stacks 06YU (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedLeftUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :
    (tensor Λ T).obj (tensorUnit Λ T, M) ≅ M :=
  @MonoidalCategoryStruct.leftUnitor _ _
    (Monoidal.transportStruct (derivedEquivalence Λ T)) M


/-- The right unitor of the existing conjugate tensor.
Source: Stacks 06YU (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedRightUnitor (T : Scheme.{u}) (M : DerivedCategory (modules Λ T)) :
    (tensor Λ T).obj (M, tensorUnit Λ T) ≅ M :=
  @MonoidalCategoryStruct.rightUnitor _ _
    (Monoidal.transportStruct (derivedEquivalence Λ T)) M


/-- The regular-module unit comparison, obtained from localization and the ordinary unit.
Source: Stacks 06YU (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedRegularUnit (T : Scheme.{u}) :
    tensorUnit Λ T ≅ (DerivedCategory.singleFunctor (modules Λ T) 0).obj
      (𝟙_ (modules Λ T)) :=
  sectionLocalizationComparison Λ T
      ((HomologicalComplex.single (internalModules Λ T) (.up ℤ) 0).obj
        (𝟙_ (internalModules Λ T))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (equivalence Λ T).functor (.up ℤ) 0).app (𝟙_ (internalModules Λ T))) ≪≫
    (DerivedCategory.singleFunctor (modules Λ T) 0).mapIso (ordinaryUnitComparison Λ T)


/-- The ringed derived unit map, localizing the actual scalar-multiplication unit.
Source: Stacks 03EL and 07A4 (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback Λ f).obj (tensorUnit Λ Y) ⟶ tensorUnit Λ X :=
  (derivedPullback Λ f).map (normalizationDerivedRegularUnit Λ Y).hom ≫
    (pullback Λ f).mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single (modules Λ Y) (.up ℤ) 0).obj (𝟙_ (modules Λ Y))) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (pullback Λ f) (.up ℤ) 0).hom.app (𝟙_ (modules Λ Y))) ≫
    (DerivedCategory.singleFunctor (modules Λ X) 0).map (normalizationSectionUnit Λ f) ≫
    (normalizationDerivedRegularUnit Λ X).inv


set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the actual localized internal oplax transformation.
Source: Stacks 07A4 (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedInternalMu {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((((Functor.whiskeringLeft₂ _).obj (internalDerivedPullback Λ f)).obj
      (internalDerivedPullback Λ f)).obj (CondensedRing.derivedTensor Λ X)) ⟶
    (Functor.postcompose₂.obj (internalDerivedPullback Λ f)).obj
      (CondensedRing.derivedTensor Λ Y) :=
  inv ((CondensedRing.upperStar Λ f).leftDerivedTensorComparison)


/-- The actual internal derived unit comparison, with its functor fixed explicitly.
Source: Stacks 07A4 (blueprint: lem-pd-section-derived-tensor-normalization). -/
def normalizationDerivedInternalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (internalDerivedPullback Λ f).obj (𝟙_ (DerivedCategory (internalModules Λ Y))) ≅
      𝟙_ (DerivedCategory (internalModules Λ X)) :=
  CondensedRing.leftDerivedUpperStarUnitIso Λ f


/-- The derived section equivalence identifies the specified tensor and actual pullback maps.
Source: Stacks Project, Cohomology on Sites, Tag 07A4, lemma-pullback-tensor-product
(blueprint: lem-pd-section-derived-tensor-normalization).

Proof, following the seven steps of the node.
1. The exact ordinary internal-section tensor comparison identifies flat objects,
   acyclic complexes, signed totals and K-flat complexes. Its inverse therefore
   identifies the resolving flat-term K-flat subcategories. Site tensor descent
   gives the localization equivalence and full faithfulness on pairs of representatives.
   The sheaf-tensor hypotheses hold on the pro-etale site by the sheafified closed
   tensor over the integers; site objects and module sections have universe u+1.
2. Localize the ordinary total comparison and conjugate by the internal and section
   tensor resolution maps. Two-variable localization extends it uniquely, with its
   inverse, to tensorComparison. Its defining square is TensorRepresentativeCondition.
3. The regular module in degree zero is flat and K-flat, since its tensor functor
   is the identity via the unitors. Localize its ordinary unit comparison. The
   associators and unitors agree on totals; localization faithfulness, successively
   in each variable, extends these diagrams to all derived objects.
4. Totalize the ordinary normalized oplax arrow. Pullback, being a left adjoint,
   preserves its direct sums. On each (p,q) summand the map splits the scalar as
   s and 1. Naturality respects both differential components, with the same sign
   (-1)^p. The ordinary normalization identifies this with the actual internal map.
5. Pullback preserves flat-term K-flat representatives. Its resolution maps are
   invertible on each representative and its total tensor. Tensor comparison descent
   therefore constructs the unique ringed isomorphism with this representative square.
6. The actual internal delta is defined by the same localization square. The
   push-pull normalization identifies its vertical resolution maps, and Steps 2 and 4
   identify its tensor maps and bottom arrow. Faithfulness on pairs of resolving
   representatives identifies these specified natural transformations everywhere.
7. Invert the resulting square to identify the actual lax arrow. On the regular
   degree-zero representatives the unit is the localized ordinary scalar multiplication.
   Totalization preserves the ordinary associator and unitor equations; successive
   localization faithfulness in each variable extends all three constraint diagrams.
-/
theorem section_derived_tensor_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (∀ T : Scheme.{u}, TensorRepresentativeCondition Λ T (qTensor Λ T)) ∧
    (∀ T : Scheme.{u}, TensorConstraintCondition
      (derivedFunctor Λ T) (Functor.uncurry.obj (CondensedRing.derivedTensor Λ T))
      (tensor Λ T) (𝟙_ (DerivedCategory (internalModules Λ T))) (tensorUnit Λ T)
      (fun M N P ↦ α_ M N P) (fun M ↦ λ_ M) (fun M ↦ ρ_ M)
      (normalizationDerivedAssociator Λ T) (normalizationDerivedLeftUnitor Λ T)
      (normalizationDerivedRightUnitor Λ T) (tensorComparison Λ T).hom (𝟙 _)) ∧
    (∀ M N : DerivedCategory (internalModules Λ Y),
      (derivedEquivalence Λ X).functor.map (((internalDelta Λ f).app M).app N) ≫
          (tensorComparison Λ X).hom.app
            ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
          (tensor Λ X).map (Prod.mkHom
            ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
        (derivedPullComparison Λ f).hom.app (M ⊗ N) ≫
          (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
          (tensorPullComparison Λ f).hom.app
            ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N)) ∧
    (∀ M N : DerivedCategory (internalModules Λ Y),
      (tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).inv.app M) ((derivedPullComparison Λ f).inv.app N)) ≫
          (tensorComparison Λ X).inv.app
            ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
          (derivedEquivalence Λ X).functor.map
            (((normalizationDerivedInternalMu Λ f).app M).app N) =
        (tensorPullComparison Λ f).inv.app
            ((derivedEquivalence Λ Y).functor.obj M, (derivedEquivalence Λ Y).functor.obj N) ≫
          (derivedPullback Λ f).map ((tensorComparison Λ Y).inv.app (M, N)) ≫
          (derivedPullComparison Λ f).inv.app (M ⊗ N)) ∧
    ((derivedEquivalence Λ X).functor.map
        (normalizationDerivedInternalUnit Λ f).hom =
      (derivedPullComparison Λ f).hom.app (𝟙_ (DerivedCategory (internalModules Λ Y))) ≫
        normalizationDerivedSectionUnit Λ f) ∧
    TensorConstraintCondition (derivedPullback Λ f) (tensor Λ Y) (tensor Λ X)
      (tensorUnit Λ Y) (tensorUnit Λ X)
      (normalizationDerivedAssociator Λ Y) (normalizationDerivedLeftUnitor Λ Y)
      (normalizationDerivedRightUnitor Λ Y)
      (normalizationDerivedAssociator Λ X) (normalizationDerivedLeftUnitor Λ X)
      (normalizationDerivedRightUnitor Λ X)
      (tensorPullComparison Λ f).hom (normalizationDerivedSectionUnit Λ f) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
