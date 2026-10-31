/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.ExtendedCechReflectorCore
import all WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all WeilConjectures.CategoryTheory.RingedIdealGenerators
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteUnitCriterion
import all WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteImpliesUnitIso
import all WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.ProperBaseChange.BoundedAboveFlatSheafKFlatSupplement
import all WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.ProperBaseChange.KInjectiveHomComplexSupplement
import all WeilConjectures.Algebra.Homology.HomTensorDegreewise
import all WeilConjectures.Algebra.Homology.HomTensorDifferential
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorNaturality
import all WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Tactic.Basic
import all WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import all WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Mathlib.Algebra.Homology.HomologySequenceLemmas
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import all Mathlib.RingTheory.Localization.BaseChange
import all WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import all WeilConjectures.Algebra.Homology.KFlatComparison
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import all Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import all WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import all WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import all Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import all WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import all WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import all Mathlib.Data.Fintype.EquivFin
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all Mathlib.CategoryTheory.Sites.LocalProperties
import all WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
import all WeilConjectures.AlgebraicGeometry.ExtendedCechUnitIsoImpliesComplete
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import all WeilConjectures.CategoryTheory.RingedSiteLocalization
import all Mathlib.CategoryTheory.Sites.LeftExact
import all WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import all WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all Mathlib.RingTheory.Ideal.Span
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import all Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import all WeilConjectures.Algebra.Homology.HomTensorTotal
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import all WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Preadditive.Biproducts
import all WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import all Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Module.LocalizedModule.Basic
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import all Mathlib.Algebra.Category.ModuleCat.Biproducts
import all WeilConjectures.RingTheory.TwoLocalizationExact
import all Mathlib.RingTheory.Coprime.Lemmas
import all Mathlib.Algebra.Exact.Basic
import all Mathlib.Tactic.LinearCombination
import all Mathlib.Tactic.Ring
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import all WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import all WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import all WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import all WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import all WeilConjectures.CategoryTheory.SliceAwayLocalization
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.RingTheory.Flat.Localization
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.AlgebraicGeometry.FiniteGeneratorsLocalSpan
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.CategoryTheory.Ringed.RingedImageIdealFiniteType
import WeilConjectures.CategoryTheory.Augmented.AugmentedCechObjectPullback
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonIndependent

/-! # Pullback of augmented extended Cech tensor actions

Source: Stacks Project, algebraization.tex, Tag 0A0G, the final pullback identity,
and sites-cohomology.tex, Tags 07A4 and 08J9.
(blueprint: lem-weil-pbc-augmented-cech-tensor-pullback).
-/

@[expose] public section

set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u wX wY

open CategoryTheory CategoryTheory.Limits WeilConjectures
open scoped MonoidalCategory

namespace CategoryTheory

private theorem inverseTranspose_eq
    {D : Type*} [Category D] (H : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H) (T P Q : D)
    (η : T ⟶ H.obj (Opposite.op P, Q)) :
    ((S.adjunction P).homEquiv T Q).symm η =
      S.tensor.map (Prod.mkHom η (𝟙 P)) ≫ (S.adjunction P).counit.app Q := by
  let := S.monoidal
  simp [CoefficientClosedStructure.tensor, Adjunction.homEquiv,
    MonoidalCategory.tensor]

private theorem inverseTranspose_precomposition
    {D : Type*} [Category D] (H : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H) (T P P' : D) (f : P' ⟶ P)
    (η : T ⟶ H.obj (Opposite.op P, T)) :
    S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ ((S.adjunction P).homEquiv T T).symm η =
      ((S.adjunction P').homEquiv T T).symm
        (η ≫ H.map (Prod.mkHom f.op (𝟙 T))) := by
  let := S.monoidal
  have he :
      (H.map (Prod.mkHom f.op (𝟙 T)) ⊗ₘ 𝟙 P') ≫ (S.adjunction P').counit.app T =
        (𝟙 (H.obj (Opposite.op P, T)) ⊗ₘ f) ≫ (S.adjunction P).counit.app T := by
    simpa [CoefficientClosedStructure.evaluation] using S.evaluation_naturality P P' T f
  simp only [inverseTranspose_eq]
  change (𝟙 T ⊗ₘ f) ≫ ((η ⊗ₘ 𝟙 P) ≫ _) = ((η ≫ _) ⊗ₘ 𝟙 P') ≫ _
  symm
  calc
    _ = (η ⊗ₘ 𝟙 P') ≫
        ((H.map (Prod.mkHom f.op (𝟙 T)) ⊗ₘ 𝟙 P') ≫
          (S.adjunction P').counit.app T) := by simp
    _ = (η ⊗ₘ 𝟙 P') ≫
        ((𝟙 (H.obj (Opposite.op P, T)) ⊗ₘ f) ≫ (S.adjunction P).counit.app T) := by
      rw [he]
    _ = _ := by
      simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
        Category.comp_id, Category.id_comp]

private def tensorRightComparison
    {D E : Type*} [Category D] [Category E]
    {HY : Dᵒᵖ × D ⥤ D} {HX : Eᵒᵖ × E ⥤ E}
    (SY : CoefficientClosedStructure HY) (SX : CoefficientClosedStructure HX)
    (L : D ⥤ E) (α : SY.tensor ⋙ L ≅ (L.prod L) ⋙ SX.tensor)
    (KY : D) (KX : E) (d : L.obj KY ≅ KX) :
    @MonoidalCategory.tensorRight _ _ SY.monoidal KY ⋙ L ≅
      L ⋙ @MonoidalCategory.tensorRight _ _ SX.monoidal KX :=
    NatIso.ofComponents
      (fun T ↦ α.app (T, KY) ≪≫ SX.tensor.mapIso ((Iso.refl (L.obj T)).prod d)) (by
        intro T T' g
        have ha := α.hom.naturality (Prod.mkHom g (𝟙 KY))
        simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom,
          Functor.comp_map]
        have hy : (@MonoidalCategory.tensorRight _ _ SY.monoidal KY).map g =
            SY.tensor.map (Prod.mkHom g (𝟙 KY)) := by
          let := SY.monoidal
          exact (MonoidalCategory.tensorHom_id g KY).symm
        have hx : (@MonoidalCategory.tensorRight _ _ SX.monoidal KX).map (L.map g) =
            SX.tensor.map (Prod.mkHom (L.map g) (𝟙 KX)) := by
          let := SX.monoidal
          exact (MonoidalCategory.tensorHom_id (L.map g) KX).symm
        rw [hy, hx]
        change L.map (SY.tensor.map (Prod.mkHom g (𝟙 KY))) ≫
            (α.hom.app (T', KY) ≫ SX.tensor.map (Prod.mkHom (𝟙 (L.obj T')) d.hom)) =
          (α.hom.app (T, KY) ≫ SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) d.hom)) ≫
            SX.tensor.map (Prod.mkHom (L.map g) (𝟙 KX))
        change L.map (SY.tensor.map (Prod.mkHom g (𝟙 KY))) ≫ α.hom.app (T', KY) =
          α.hom.app (T, KY) ≫ SX.tensor.map (Prod.mkHom (L.map g) (L.map (𝟙 KY))) at ha
        rw [← Category.assoc, ha, Functor.map_id]
        simp only [Category.assoc, ← SX.tensor.map_comp]
        congr 2
        ext <;> simp)

private theorem augmented_tensor_comparison
    {D E : Type*} [Category D] [Category E]
    (HY : Dᵒᵖ × D ⥤ D) (HX : Eᵒᵖ × E ⥤ E)
    (SY : CoefficientClosedStructure HY) (SX : CoefficientClosedStructure HX)
    (L : D ⥤ E) (UY : D) (UX : E)
    (ηY : ∀ T : D, T ⟶ HY.obj (Opposite.op UY, T))
    (ηX : ∀ T : E, T ⟶ HX.obj (Opposite.op UX, T))
    (α : SY.tensor ⋙ L ≅ (L.prod L) ⋙ SX.tensor) (j : L.obj UY ≅ UX)
    (hu : ∀ T : D,
      α.hom.app (T, UY) ≫ SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) j.hom) ≫
        ((SX.adjunction UX).homEquiv (L.obj T) (L.obj T)).symm (ηX (L.obj T)) =
      L.map (((SY.adjunction UY).homEquiv T T).symm (ηY T)))
    (KY : D) (KX : E) (εY : KY ⟶ UY) (εX : KX ⟶ UX)
    (d : L.obj KY ≅ KX) (hd : d.hom ≫ εX = L.map εY ≫ j.hom) :
    ∃ c : @MonoidalCategory.tensorRight _ _ SY.monoidal KY ⋙ L ≅
        L ⋙ @MonoidalCategory.tensorRight _ _ SX.monoidal KX,
      ∀ T : D, c.hom.app T ≫
          ((SX.adjunction KX).homEquiv (L.obj T) (L.obj T)).symm
            (ηX (L.obj T) ≫ HX.map (Prod.mkHom εX.op (𝟙 (L.obj T)))) =
        L.map (((SY.adjunction KY).homEquiv T T).symm
          (ηY T ≫ HY.map (Prod.mkHom εY.op (𝟙 T)))) := by
  let c := tensorRightComparison SY SX L α KY KX d
  refine ⟨c, ?_⟩
  intro T
  rw [← inverseTranspose_precomposition HX SX (L.obj T) UX KX εX (ηX (L.obj T)),
    ← inverseTranspose_precomposition HY SY T UY KY εY (ηY T)]
  change (α.hom.app (T, KY) ≫ SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) d.hom)) ≫
      (SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) εX) ≫ _) =
    L.map (SY.tensor.map (Prod.mkHom (𝟙 T) εY) ≫ _)
  have hn := α.hom.naturality (Prod.mkHom (𝟙 T) εY)
  change L.map (SY.tensor.map (Prod.mkHom (𝟙 T) εY)) ≫ α.hom.app (T, UY) =
    α.hom.app (T, KY) ≫ SX.tensor.map (Prod.mkHom (L.map (𝟙 T)) (L.map εY)) at hn
  rw [Functor.map_id] at hn
  have ht : SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) d.hom) ≫
      SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) εX) =
      SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) (L.map εY)) ≫
        SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) j.hom) := by
    simp only [← SX.tensor.map_comp, prod_comp, Category.id_comp, hd]
  simp only [Category.assoc, L.map_comp]
  rw [← Category.assoc (SX.tensor.map _), ht]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, hu]

private theorem inverseTransposeUnitIso
    {D : Type*} [Category D] (F H : D ⥤ D) (adj : F ⊣ H) (η : 𝟭 D ≅ H) :
    ∃ s : F ≅ 𝟭 D, ∀ T : D, s.hom.app T = (adj.homEquiv T T).symm (η.hom.app T) := by
  let adj' : 𝟭 D ⊣ H := Adjunction.id.ofNatIsoRight η
  let s := adj.leftAdjointUniq adj'
  refine ⟨s, ?_⟩
  intro T
  apply (adj.homEquiv T T).injective
  rw [Equiv.apply_symm_apply]
  change adj.homEquiv T T ((adj.leftAdjointUniq adj').hom.app T) = _
  calc
    _ = adj'.unit.app T := Adjunction.homEquiv_leftAdjointUniq_hom_app adj adj' T
    _ = η.hom.app T := by simp [adj', Adjunction.ofNatIsoRight, Adjunction.id]

private theorem normalize_tensor_comparison
    {D E : Type*} [Category D] [Category E]
    {HY : Dᵒᵖ × D ⥤ D} {HX : Eᵒᵖ × E ⥤ E}
    (SY : CoefficientClosedStructure HY) (SX : CoefficientClosedStructure HX)
    (L : D ⥤ E) (UY : D) (UX : E)
    (ηY : 𝟭 D ≅ Prod.sectR (Opposite.op UY) D ⋙ HY)
    (ηX : 𝟭 E ≅ Prod.sectR (Opposite.op UX) E ⋙ HX)
    (α : SY.tensor ⋙ L ≅ (L.prod L) ⋙ SX.tensor) (j : L.obj UY ≅ UX) :
    ∃ α' : SY.tensor ⋙ L ≅ (L.prod L) ⋙ SX.tensor,
      ∀ T : D, α'.hom.app (T, UY) ≫
          SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) j.hom) ≫
          ((SX.adjunction UX).homEquiv (L.obj T) (L.obj T)).symm
            (ηX.hom.app (L.obj T)) =
        L.map (((SY.adjunction UY).homEquiv T T).symm (ηY.hom.app T)) := by
  obtain ⟨sY, hsY⟩ := inverseTransposeUnitIso _ _ (SY.adjunction UY) ηY
  obtain ⟨sX, hsX⟩ := inverseTransposeUnitIso _ _ (SX.adjunction UX) ηX
  let b := tensorRightComparison SY SX L α UY UX j
  let t : L ≅ L := L.leftUnitor.symm ≪≫ Functor.isoWhiskerRight sY.symm L ≪≫ b ≪≫
    Functor.isoWhiskerLeft L sX ≪≫ L.rightUnitor
  let α' := α ≪≫ Functor.isoWhiskerRight (NatIso.prod t.symm (Iso.refl L)) SX.tensor
  refine ⟨α', ?_⟩
  intro T
  rw [← hsX, ← hsY]
  have ht : L.map (sY.hom.app T) ≫ t.hom.app T =
      α.hom.app (T, UY) ≫ SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) j.hom) ≫
        sX.hom.app (L.obj T) := by
    dsimp only [t, b, tensorRightComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
    simp only [Category.id_comp, ← L.map_comp_assoc,
      Iso.hom_inv_id_app, L.map_id]
    simp
  have hn := sX.hom.naturality (t.inv.app T)
  have hm : (@MonoidalCategory.tensorRight _ _ SX.monoidal UX).map (t.inv.app T) =
      SX.tensor.map (Prod.mkHom (t.inv.app T) (𝟙 UX)) := by
    let := SX.monoidal
    exact (MonoidalCategory.tensorHom_id (t.inv.app T) UX).symm
  rw [hm] at hn
  change (α.hom.app (T, UY) ≫
    SX.tensor.map (Prod.mkHom (t.inv.app T) (𝟙 (L.obj UY)))) ≫ _ ≫ _ = _
  have hi : SX.tensor.map (Prod.mkHom (t.inv.app T) (𝟙 (L.obj UY))) ≫
        SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) j.hom) =
      SX.tensor.map (Prod.mkHom (𝟙 (L.obj T)) j.hom) ≫
        SX.tensor.map (Prod.mkHom (t.inv.app T) (𝟙 UX)) := by
    simp only [← SX.tensor.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (SX.tensor.map _), hi]
  simp only [Category.assoc]
  rw [hn, ← reassoc_of% ht]
  simp

set_option maxHeartbeats 1600000 in
-- The image ideal interface elaborates several repeated underlying-sheaf functors.
/-- Derived pullback intertwines the augmented Cech tensor actions for an ideal and
its generated image. The augmentation equation is expressed using inverse tensor-Hom transposes.
No completion reflector or direct-image/completion comparison is part of this statement.

Source: Stacks Project, algebraization.tex, Tag 0A0G, final Koszul pullback identity;
sites-cohomology.tex, Tags 07A4 (derived tensor pullback) and 08J9 (tensor-Hom).
(blueprint: lem-weil-pbc-augmented-cech-tensor-pullback).

Proof: first transport local finite generation to the structural image ideal.
The augmented-object pullback theorem supplies a coefficient-ring isomorphism
and an isomorphism between the two augmented Cech objects commuting with their
augmentations. Independently, compute the supplied derived pullback on flat-term
K-flat representatives to obtain a bifunctorial tensor comparison, allowing the
two localization universes to be independent.

For each supplied closed structure, inverse transposition of the canonical
internal-Hom unit gives a natural isomorphism from tensoring with the coefficient
ring to the identity. The tensor comparison and the coefficient-ring comparison
therefore determine a natural automorphism of L. Postcompose the tensor comparison
with the tensor of its inverse and the identity. This normalizes the comparison
at the coefficient ring without assuming monoidal coherence for L.

Restrict this normalized bifunctor comparison to the target Cech object and
postcompose with the augmented-object isomorphism in the second tensor variable.
This gives the required natural isomorphism c. Naturality in the augmentation,
the augmented-object commuting square, and the normalization at the coefficient
ring identify its composites with the inverse transposes of the two completion
units. The inverse-transpose formula is precisely tensoring with the augmentation
followed by inverse transposition of the coefficient-ring unit. -/
theorem ringed_augmentedCech_tensor_pullback
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : X, HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (L : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wX} RX)
    (a : L ⊣ Rf)
    (SY : CoefficientClosedStructure (derivedInternalHom.{u, wY} J RY))
    (SX : CoefficientClosedStructure (derivedInternalHom.{u, wX} K RX)) :
    IX.IsFiniteType ∧
    ∀ (KX : ringedSiteComplex RX) (εX : KX ⟶ ringedSiteRingComplex RX),
      HasLocalExtendedCechDescription.{u, wX} RX IX ιX KX εX →
    ∀ (KY : ringedSiteComplex RY) (εY : KY ⟶ ringedSiteRingComplex RY),
      HasLocalExtendedCechDescription.{u, wY} RY IY ιY KY εY →
    ∃ c : @MonoidalCategory.tensorRight _ _ SY.monoidal
          (DerivedCategory.Q.{wY}.obj KY) ⋙ L ≅
        L ⋙ @MonoidalCategory.tensorRight _ _ SX.monoidal
          (DerivedCategory.Q.{wX}.obj KX),
      ∀ T : ringedSiteDerived.{u, wY} RY, c.hom.app T ≫
          ((SX.adjunction (DerivedCategory.Q.{wX}.obj KX)).homEquiv (L.obj T) (L.obj T)).symm
            (ringedCechCompletionUnit.{u, wX} RX KX εX (L.obj T)) =
        L.map (((SY.adjunction (DerivedCategory.Q.{wY}.obj KY)).homEquiv T T).symm
          (ringedCechCompletionUnit.{u, wY} RY KY εY T)) := by
  have hfin := ringed_imageIdeal_finiteType RY RX f IY ιY IX ιX hImage
  let : IX.IsFiniteType := hfin
  obtain ⟨j, hj⟩ := ringed_augmentedCech_object_pullback
    RY RX f IY ιY IX ιX hImage Rf ρ hRf hCompute L a
  obtain ⟨α⟩ := ringed_tensor_comparison_independent RY RX f Rf ρ hRf hCompute L a SY SX
  let ηY := derivedHomUnitIso.{u, wY} RY
  let ηX := derivedHomUnitIso.{u, wX} RX
  obtain ⟨α', hα'⟩ := normalize_tensor_comparison SY SX L
    (DerivedCategory.Q.{wY}.obj (ringedSiteRingComplex RY))
    (DerivedCategory.Q.{wX}.obj (ringedSiteRingComplex RX)) ηY ηX α j
  refine ⟨hfin, ?_⟩
  intro KX εX hKX KY εY hKY
  obtain ⟨d, hd⟩ := hj KX εX hKX KY εY hKY
  exact augmented_tensor_comparison _ _ SY SX L _ _
    (ringedDerivedHomUnit RY) (ringedDerivedHomUnit RX) α' j hα'
    (DerivedCategory.Q.{wY}.obj KY) (DerivedCategory.Q.{wX}.obj KX)
    (DerivedCategory.Q.{wY}.map εY) (DerivedCategory.Q.{wX}.map εX) d hd

end CategoryTheory
