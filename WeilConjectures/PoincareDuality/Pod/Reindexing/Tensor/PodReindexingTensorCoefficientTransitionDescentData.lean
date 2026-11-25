/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.PoincareDuality.PodReindexCoefficientTransition.PodReindexingTensorCoefficientTransitionCore
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingScalarTensorChainSquare
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

/-! # Representative maps for scalar/reindexing tensor descent

Exactness properties of reindexing and scalar extension of integral tower modules, the induced
functors and comparisons on good complexes, the reindexing, scalar and mixed tensor chains on
good representatives, and `podCoefficientExactSquareChain`, which lifts a square of complex maps
along a commutative square of exact functors to the derived categories.

## References

* Stacks Project, Tags 03EL, 05RU, 06YY, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Reindexing of integral tower modules along an isomorphism `g` is additive. -/
theorem podTensorReindexAdditive (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoReductionIntegralInverse l E g).Additive := by
  let c := isoReductionCompletedMap l E g
  let : IsIso c.hom := c.isIso_hom
  exact isoSectionwiseModuleInverseImage_additive.{u, u} g c.hom

/-- Scalar extension of integral tower modules along `ι` preserves zero morphisms. -/
theorem podTensorScalarZero (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    (integralOrdinaryScalar l E L ι W).PreservesZeroMorphisms := by
  let : (integralOrdinaryScalar l E L ι W).Additive :=
    integralOrdinaryScalar_additive l E L ι W
  infer_instance

/-- Reindexing along `g` followed by scalar extension along `ι` preserves zero morphisms. -/
theorem podTensorMixedLeftZero (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (isoReductionIntegralInverse l E g ⋙
      integralOrdinaryScalar l E L ι X).PreservesZeroMorphisms := by
  let : (isoReductionIntegralInverse l E g).PreservesZeroMorphisms := by
    let : (isoReductionIntegralInverse l E g).Additive := podTensorReindexAdditive l E g
    infer_instance
  let : (integralOrdinaryScalar l E L ι X).PreservesZeroMorphisms := podTensorScalarZero l E L ι X
  exact Functor.preservesZeroMorphisms_comp _ _

/-- Scalar extension along `ι` followed by reindexing along `g` preserves zero morphisms. -/
theorem podTensorMixedRightZero (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    (integralOrdinaryScalar l E L ι Y ⋙
      isoReductionIntegralInverse l L g).PreservesZeroMorphisms := by
  let : (isoReductionIntegralInverse l L g).PreservesZeroMorphisms := by
    let : (isoReductionIntegralInverse l L g).Additive := podTensorReindexAdditive l L g
    infer_instance
  let : (integralOrdinaryScalar l E L ι Y).PreservesZeroMorphisms := podTensorScalarZero l E L ι Y
  exact Functor.preservesZeroMorphisms_comp _ _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  integralOperationsTensorTowerFunctor scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos

/-- Reindexing of integral tower modules along an isomorphism `g` preserves finite limits. -/
theorem podTensorReindexLimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteLimits (isoReductionIntegralInverse l E g) := by
  let c := isoReductionCompletedMap l E g
  let : IsIso c.hom := c.isIso_hom
  exact isoSectionwiseModuleInverseImage_limits.{u, u} g c.hom

/-- Reindexing of integral tower modules along an isomorphism `g` preserves finite colimits. -/
theorem podTensorReindexColimits (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    PreservesFiniteColimits (isoReductionIntegralInverse l E g) := by
  let c := isoReductionCompletedMap l E g
  let : IsIso c.hom := c.isIso_hom
  exact isoSectionwiseModuleInverseImage_colimits.{u, u} g c.hom

attribute [local instance] podTensorReindexAdditive podTensorScalarZero
  podTensorMixedLeftZero podTensorMixedRightZero podTensorReindexLimits podTensorReindexColimits

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory

attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory

/-- Termwise scalar extension along `ι`, as a functor between good complexes over `W`. -/
def podTensorScalarGoodFunctor (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :=
  (integralOperationsGoodComplex l L W).lift
    ((integralOperationsGoodComplex l E W).ι ⋙
      (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ))
    (fun P ↦ scalarGood l E L ι W P)

/-- The comparison between derived scalar extension of the localization of a good complex and
the localization of its termwise scalar extension. -/
def podTensorScalarGoodComparison (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u}) :
    integralOperationsGoodLocalization l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      podTensorScalarGoodFunctor l E L ι W ⋙ integralOperationsGoodLocalization l L W :=
  isoWhiskerLeft (integralOperationsGoodComplex l E W).ι
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors

/-- The comparison between derived reindexing of the localization of a good complex and the
localization of its termwise reindexing. -/
def podTensorReindexGoodComparison {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (D : PodCompletionReindex l E g) :
    integralOperationsGoodLocalization l E Y ⋙ podOrdinaryReindex l E g ≅
      podGoodReindex l E g D ⋙ integralOperationsGoodLocalization l E X :=
  isoWhiskerLeft (integralOperationsGoodComplex l E Y).ι
    (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors

attribute [local implicit_reducible] podTensorScalarGoodFunctor podTensorScalarGoodComparison
  podTensorReindexGoodComparison

/-- The natural isomorphism of good complexes between reindexing then scalar extension and
scalar extension then reindexing, given componentwise by the complex transition `S.complex`. -/
def podTensorGoodCoefficientTransition
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : PodCompletionReindex l E g)
    (D' : PodCompletionReindex l L g)
    (S : PodReindexCoefficientTransition l E L ι g D D') :
    podGoodReindex l E g D ⋙ podTensorScalarGoodFunctor l E L ι X ≅
      podTensorScalarGoodFunctor l E L ι Y ⋙ podGoodReindex l L g D' :=
  NatIso.ofComponents
    (fun P ↦ (integralOperationsGoodComplex l L X).isoMk
      ((S.complex l E g L ι D D').app P.obj)) (by
        intro P Q a
        apply (integralOperationsGoodComplex l L X).ι.map_injective
        exact (S.complex l E g L ι D D').hom.naturality a.hom)

/-- The derived reindexing chain map from the reindexed tensor product of good complexes
`P, Q` to the tensor product of their reindexings. -/
def podTensorTensorReindexDerivedChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (podOrdinaryReindex l E g).obj ((integralOperationsTensorOnGood l E Y).obj (P, Q)) ⟶
      (integralOperationsTensorOnGood l E X).obj
        ((podGoodReindex l E g D).obj P, (podGoodReindex l E g D).obj Q) :=
  (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
      ((integralOperationsTensorComplexFunctor l E Y).obj (P.obj, Q.obj)) ≫
    DerivedCategory.Q.map (podReindexTensorChain l E g D T P Q)

/-- The derived scalar chain map from the scalar extension of the tensor product of good
complexes `P, Q` to the tensor product of their scalar extensions. -/
def podTensorTensorScalarDerivedChain
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι W).obj
        ((integralOperationsTensorOnGood l E W).obj (P, Q)) ⟶
      (integralOperationsTensorOnGood l L W).obj
        ((podTensorScalarGoodFunctor l E L ι W).obj P, (podTensorScalarGoodFunctor l E L ι W).obj
    Q) :=
  (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
      ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj)) ≫
    DerivedCategory.Q.map (scalarTensorChain l E L ι W P.obj Q.obj)

/-- The derived mixed chain map: the reindexing of the scalar chain followed by the reindexing
chain at the scalar-extended pair. -/
def podTensorTensorMixedDerivedChain
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D' : PodCompletionReindex l L g)
    (T' : PodCompletedTensorReindex l L g D')
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι Y ⋙ podOrdinaryReindex l L g).obj
        ((integralOperationsTensorOnGood l E Y).obj (P, Q)) ⟶
      (integralOperationsTensorOnGood l L X).obj
        ((podGoodReindex l L g D').obj ((podTensorScalarGoodFunctor l E L ι Y).obj P),
          (podGoodReindex l L g D').obj ((podTensorScalarGoodFunctor l E L ι Y).obj Q)) :=
  (podOrdinaryReindex l L g).map (podTensorTensorScalarDerivedChain l E L ι Y P Q) ≫
    podTensorTensorReindexDerivedChain l L g D' T'
      ((podTensorScalarGoodFunctor l E L ι Y).obj P) ((podTensorScalarGoodFunctor l E L ι Y).obj Q)

/-- The property of a good complex that its image in the derived category is constructible. -/
def podTensorGoodConstructible (W : Scheme.{u}) :
    ObjectProperty (integralOperationsGoodComplex l E W).FullSubcategory :=
  fun P ↦ sfIntegralConstructible l E W (DerivedCategory.Q.obj P.obj)

/-- The localization functor from constructible good complexes to the constructible derived
category. -/
def podTensorGoodConstructibleLocalization (W : Scheme.{u}) :
    (podTensorGoodConstructible l E W).FullSubcategory ⥤ sfIntegralConstructibleCategory l E W :=
  (sfIntegralConstructible l E W).lift
    ((podTensorGoodConstructible l E W).ι ⋙ integralOperationsGoodLocalization l E W)
    (fun P ↦ P.property)

private theorem goodConstructibleLocalization_essSurj (W : Scheme.{u}) :
    (podTensorGoodConstructibleLocalization l E W).EssSurj := by
  let q := integralOperationsGoodLocalization l E W
  let V := (HomologicalComplex.quasiIso (integralTowerModules l E W) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E W).ι
  let : q.IsLocalization V := integralOperationsGoodLocalization_isLocalization l E W
  let : q.EssSurj := Localization.essSurj q V
  refine ⟨fun M ↦ ?_⟩
  let P := q.objPreimage M.obj
  let e := q.objObjPreimageIso M.obj
  have hP : podTensorGoodConstructible l E W P :=
    (sfIntegralConstructible l E W).prop_of_iso e.symm M.property
  exact ⟨⟨P, hP⟩, ⟨(sfIntegralConstructible l E W).isoMk e⟩⟩

/-- The natural isomorphism, given by `T.tensor`, between the reindexing of a completed tensor
product of constructible objects and the completed tensor product of their reindexings. -/
def podTensorTensorReindexIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Naturality l E g D T) :
    ((sfIntegralConstructible l E Y).ι.prod (sfIntegralConstructible l E Y).ι) ⋙
        integralCompletedTensor l E Y ⋙ podOrdinaryReindex l E g ≅
      (((sfIntegralConstructible l E Y).ι ⋙ podOrdinaryReindex l E g).prod
        ((sfIntegralConstructible l E Y).ι ⋙ podOrdinaryReindex l E g)) ⋙
        integralCompletedTensor l E X :=
  NatIso.ofComponents (fun M ↦ T.tensor M.1 M.2)
    (by intro M N f; exact _hT _ _ _ _ f.1 f.2)

/-- The natural isomorphism, given by `scalarTensorOrdinary` followed by `T'.tensor`, between the
scalar extension and reindexing of a completed tensor product of constructible objects and the
completed tensor product of their scalar extensions and reindexings. -/
def podTensorMixedTensorIso
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (D : PodCompletionReindex l E g)
    (D' : PodCompletionReindex l L g) (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Naturality l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D') :
    ((sfIntegralConstructible l E Y).ι.prod (sfIntegralConstructible l E Y).ι) ⋙
        integralCompletedTensor l E Y ⋙ integralOrdinaryDerivedScalar l E L ι Y ⋙
          podOrdinaryReindex l L g ≅
      (((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y ⋙
          podOrdinaryReindex l L g).prod
        ((sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y ⋙
          podOrdinaryReindex l L g)) ⋙ integralCompletedTensor l L X := by
  let I := (sfIntegralConstructible l E Y).ι
  let H := integralOrdinaryDerivedScalar l E L ι Y ⋙ podOrdinaryReindex l L g
  let C := (I ⋙ H).prod (I ⋙ H)
  let U₂ := integralCompletedTensor l L X
  exact NatIso.ofComponents
    (fun M ↦ (podOrdinaryReindex l L g).mapIso
      ((scalarTensorOrdinary l E L ι Y).app (M.1.obj, M.2.obj)) ≪≫
      T'.tensor ⟨_, S.sourceConstructible M.1⟩ ⟨_, S.sourceConstructible M.2⟩) (by
        intro M N f
        dsimp only [Iso.trans_hom, Functor.mapIso_hom]
        have hn := (scalarTensorOrdinary l E L ι Y).hom.naturality
          (Prod.mkHom f.1.hom f.2.hom)
        dsimp only [Functor.comp_map, Functor.prod_map] at hn
        change (podOrdinaryReindex l L g).map
            ((integralOrdinaryDerivedScalar l E L ι Y).map
              ((integralCompletedTensor l E Y).map (Prod.mkHom f.1.hom f.2.hom))) ≫
            (podOrdinaryReindex l L g).map _ ≫ _ = _
        simp only [Iso.app_hom] at ⊢
        rw [← Functor.map_comp_assoc, hn, Functor.map_comp, Category.assoc]
        have ht := _hT'
          ⟨_, S.sourceConstructible M.1⟩ ⟨_, S.sourceConstructible M.2⟩
          ⟨_, S.sourceConstructible N.1⟩ ⟨_, S.sourceConstructible N.2⟩
          (ObjectProperty.homMk ((integralOrdinaryDerivedScalar l E L ι Y).map f.1.hom))
          (ObjectProperty.homMk ((integralOrdinaryDerivedScalar l E L ι Y).map f.2.hom))
        simpa only [C, U₂, I, H, Functor.comp_map, Functor.prod_map,
          ObjectProperty.ι_map, ObjectProperty.homMk_hom, Category.assoc] using
          congrArg (fun z ↦ (podOrdinaryReindex l L g).map
            ((scalarTensorOrdinary l E L ι Y).hom.app (M.1.obj, M.2.obj)) ≫ z) ht)

private theorem exactSquareFactors
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso H I).symm).hom.app
        (DerivedCategory.Q.obj K)) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fac F G K
  have hi₁ : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hi₁, DerivedCategory.Q.map_id, Category.comp_id] at h₁
  have h₂ := Functor.mapDerivedCategoryCompIso_fac H I K
  have hi₂ : (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ I))
      (.up ℤ)).hom.app K = 𝟙 _ := rfl
  erw [hi₂, DerivedCategory.Q.map_id, Category.comp_id] at h₂
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F G).inv.app
    (DerivedCategory.Q.obj K))).1
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [h₂, Functor.mapDerivedCategoryNatIso_fac, ← h₁]
  simp only [NatIso.mapHomologicalComplex]
  repeat' erw [Category.assoc]

/-- A commutative square `s : F ⋙ G ≅ H ⋙ I` of exact functors lifts a commuting square of
complex maps to the derived categories, including the derived comparison factors. -/
theorem podCoefficientExactSquareChain
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (I : C ⥤ D) [I.Additive] [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (s : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ)
    (P : CochainComplex B ℤ) (Q : CochainComplex C ℤ)
    (Z Z' : CochainComplex D ℤ)
    (c : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ P)
    (d : (G.mapHomologicalComplex (.up ℤ)).obj P ⟶ Z)
    (e : (H.mapHomologicalComplex (.up ℤ)).obj K ⟶ Q)
    (f : (I.mapHomologicalComplex (.up ℤ)).obj Q ⟶ Z') (r : Z ⟶ Z')
    (hc : (G.mapHomologicalComplex (.up ℤ)).map c ≫ d ≫ r =
      (NatIso.mapHomologicalComplex s (.up ℤ)).hom.app K ≫
        (I.mapHomologicalComplex (.up ℤ)).map e ≫ f) :
    G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map c) ≫
      G.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map d ≫
      DerivedCategory.Q.map r =
    ((F.mapDerivedCategoryCompIso G ≪≫ mapDerivedCategoryNatIso s ≪≫
        (H.mapDerivedCategoryCompIso I).symm).hom.app (DerivedCategory.Q.obj K)) ≫
      I.mapDerivedCategory.map
        (H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map e) ≫
      I.mapDerivedCategoryFactors.hom.app Q ≫ DerivedCategory.Q.map f := by
  have hn := G.mapDerivedCategoryFactors.hom.naturality c
  have hr := I.mapDerivedCategoryFactors.hom.naturality e
  dsimp only [Functor.comp_map] at hn hr
  rw [G.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, hc]
  erw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]
  erw [← reassoc_of% (exactSquareFactors F G H I s K),
    ← reassoc_of% hr]
  simp only [Functor.map_comp, Category.assoc]

private theorem faithfulRestriction
    {R D C : Type*} [Category* R] [Category* D] [Category* C]
    (q : R ⥤ D) [q.EssSurj] : ((whiskeringLeft R D C).obj q).Faithful := by
  refine ⟨fun {F G} α β h ↦ ?_⟩
  apply NatTrans.ext
  funext M
  let P := q.objPreimage M
  let e := q.objObjPreimageIso M
  have hp := NatTrans.congr_app h P
  change α.app (q.obj P) = β.app (q.obj P) at hp
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, hp]

attribute [local implicit_reducible] podTensorGoodConstructibleLocalization
    podTensorGoodConstructible podTensorMixedTensorIso
  podTensorGoodCoefficientTransition podTensorTensorReindexDerivedChain
    podTensorTensorScalarDerivedChain
  podTensorTensorMixedDerivedChain

end WeilConjectures
