/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRestrictedTowerNaturality
import all WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined

/-! # Canonical derived restriction and evaluation comparisons for reindexing

Let `g : X ⟶ Y` be an isomorphism of schemes. We define the derived comparisons of reindexing
along `g` with derived restriction of scalars from a finite coefficient level and with finite
evaluation of coefficient systems. Both are induced by strict comparisons of exact functors.

## Implementation details

The strict restriction comparison is the identity on sections. The strict evaluation comparison
is the unique one whose restriction of scalars is the restricted-tower comparison of reindexing,
which exists because restriction of scalars from a finite coefficient level is fully faithful. -/

public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Restriction of scalars from a finite coefficient level is full. -/
theorem scalarReductionRestriction_full (W : Scheme.{t}) (n : ℕ) :
    (scalarReductionRestriction l E W n).Full where
  map_surjective {M N} f := by
    let q := (sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l E W n)
    have : Presheaf.IsLocallySurjective (ProEt.topology W) q.hom :=
      completedProjection_locallySurjective l E W n
    let e := PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (J := ProEt.topology W) (M₁ := M.val) q.hom N.isSheaf
    refine ⟨⟨e.symm f.val⟩, ?_⟩
    apply SheafOfModules.hom_ext
    exact e.apply_symm_apply f.val

/-- Restriction of scalars from a finite coefficient level is faithful. -/
theorem scalarReductionRestriction_faithful (W : Scheme.{t}) (n : ℕ) :
    (scalarReductionRestriction l E W n).Faithful where
  map_injective {M N} f f' h := by
    ext U x
    exact congrArg (fun k ↦ k.val.app U x) h

/-- Restriction of scalars from a finite coefficient level is fully faithful. -/
def scalarReductionRestrictionFullyFaithful (W : Scheme.{t}) (n : ℕ) :
    (scalarReductionRestriction l E W n).FullyFaithful :=
  have := scalarReductionRestriction_full l E W n
  have := scalarReductionRestriction_faithful l E W n
  .ofFullyFaithful _

/-- The strict comparison of reindexing with restriction of scalars from level `n`. -/
def podReindexingStrictRestriction (n : ℕ) :
    scalarReductionRestriction l E Y n ⋙ isoReductionIntegralInverse l E g ≅
      isoReductionFiniteInverse l E g n ⋙ scalarReductionRestriction l E X n :=
  (isoReduction_restrictionSquare l E g n).choose

/-- The strict restriction comparison is the identity on sections. -/
theorem podReindexingStrictRestriction_apply (n : ℕ) (N : scalarReductionTarget l E Y n)
    (U : X.ProEtᵒᵖ) (x : N.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    ((podReindexingStrictRestriction l E g n).hom.app N).val.app U x = x :=
  (isoReduction_restrictionSquare l E g n).choose_spec N U x

/-- The restricted-tower comparison of reindexing at level `n`, after restriction of scalars. -/
def podReindexingRestrictedEvaluation (n : ℕ) :
    (integralComparisonSequencePullback l E g ⋙ coefficientSequenceEvaluation l E X n) ⋙
        scalarReductionRestriction l E X n ≅
      (coefficientSequenceEvaluation l E Y n ⋙ isoReductionFiniteInverse l E g n) ⋙
        scalarReductionRestriction l E X n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (integralComparisonSequencePullback l E g)
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (restrictedModuleIso l E g).symm
      ((evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n)) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (coefficientSequenceRestriction l E Y)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by simp) :
        (whiskeringRight ℕᵒᵖ _ _).obj (isoReductionIntegralInverse l E g) ⋙
            (evaluation ℕᵒᵖ (scalarReductionSource l E X)).obj (op n) ≅
          (evaluation ℕᵒᵖ (scalarReductionSource l E Y)).obj (op n) ⋙
            isoReductionIntegralInverse l E g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (eqToIso (coefficientSequenceRestriction_evaluation l E Y n))
      (isoReductionIntegralInverse l E g) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
      (podReindexingStrictRestriction l E g n) ≪≫
    (Functor.associator _ _ _).symm

/-- The strict comparison of reindexing with evaluation at level `n`. -/
def podReindexingStrictEvaluation (n : ℕ) :
    integralComparisonSequencePullback l E g ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ isoReductionFiniteInverse l E g n :=
  ((scalarReductionRestrictionFullyFaithful l E X n).whiskeringRight _).preimageIso
    (podReindexingRestrictedEvaluation l E g n)

/-- After restriction of scalars, the strict evaluation comparison is the restricted-tower
comparison. -/
theorem podReindexingStrictEvaluation_hom_app (n : ℕ) (M : coefficientSequenceModules l E Y) :
    (scalarReductionRestriction l E X n).map
        ((podReindexingStrictEvaluation l E g n).hom.app M) =
      (podReindexingRestrictedEvaluation l E g n).hom.app M :=
  congr_app (((scalarReductionRestrictionFullyFaithful l E X n).whiskeringRight _).map_preimage
    (podReindexingRestrictedEvaluation l E g n).hom) M

/-- The derived comparison of reindexing with derived restriction of scalars from level `n`. -/
def podReindexingDerivedRestriction (n : ℕ) :
    coefficientFiniteDerivedRestriction l E Y n ⋙ podOrdinaryReindex l E g ≅
      isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n :=
  Functor.mapDerivedCategorySquareIso (podReindexingStrictRestriction l E g n)

/-- The derived comparison of reindexing with derived evaluation at level `n`. -/
def podReindexingDerivedEvaluation (n : ℕ) :
    integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n :=
  Functor.mapDerivedCategorySquareIso (podReindexingStrictEvaluation l E g n)

namespace PodReindexingDerivedCanonical

/-- On a complex `I`, the derived comparison induced by a square of exact functors is the
localization of the strict comparison, up to the localization factorizations. -/
theorem squareIso_factors
    {A B B' D : Type*} [Category* A] [Category* B] [Category* B'] [Category* D]
    [Abelian A] [Abelian B] [Abelian B'] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory B'] [HasDerivedCategory D]
    (F₁ : A ⥤ B) (F₂ : B ⥤ D) (G₁ : A ⥤ B') (G₂ : B' ⥤ D)
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (I : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.inv.app I) ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj I) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app I) ≫
        G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj I) =
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app I) := by
  apply (cancel_epi (F₂.mapDerivedCategoryFactors.inv.app
    ((F₁.mapHomologicalComplex (.up ℤ)).obj I))).mp
  rw [Iso.inv_hom_id_app_assoc]
  have hF := Functor.mapDerivedCategoryCompIso_hom_app_factors F₁ F₂ I
  have hG := Functor.mapDerivedCategoryCompIso_hom_app_factors G₁ G₂ I
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hG, Functor.mapDerivedCategoryNatIso_fac]
  rw [← hF]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [F₂.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]

end PodReindexingDerivedCanonical

end WeilConjectures
