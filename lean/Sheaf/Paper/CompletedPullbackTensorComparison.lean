/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.FinitePullbackTensorComparison
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.Paper.IntegralComparisonSequenceSystems

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-completed-pullback-tensor-comparison).

## Main definitions

* `canonicalIntegralPullbackTensor` is the prescribed comparison.
* The helper declarations fix its representative normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField

section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The sequence site's actual object and morphism universes are u+1 and u.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance (priority := 3000) pullbackTensorSequenceSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} (ℕ × W.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The recorded coefficient reduction/limit adjunction and tensor models.
Source: Stacks 0941 and 07A6 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorCalculus (W : Scheme.{u}) :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose

/-- Base change on the actual ringed sequence site.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceBase {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Base change preserves the vertical covering condition.
Source: Stacks 0941, 098K (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: a vertical slice of a pulled-back sieve is the base change of its
vertical slice; pro-etale covers are stable under scheme base change. -/
@[instance] theorem pullbackTensorSequenceBase_continuous {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (pullbackTensorSequenceBase f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  exact integralComparisonSequenceBaseChange_continuous f

/-- The sequence-ring map is fixed at every level by the constant-section map.
Source: Stacks 0941 and 0H7J (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: take the existing constant-section morphism at every positive quotient.
Its naturality in quotient ring maps proves naturality also in the sequence
direction. These components define the ring-sheaf morphism; componentwise
extensionality proves uniqueness. -/
theorem pullbackTensorSequenceRing_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! ρ : coefficientSequenceCommRingSheaf l E Y ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X),
      ∀ (n : ℕ) (U : Y.ProEt),
        HEq (ρ.hom.app (op (n,U)))
          ((coefficientProEtaleDirectRingMap.{u, u} f
            (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).hom.app
              (op U)) := by
  refine ⟨integralComparisonSequenceRingMap l E f, ?_, ?_⟩
  · intro n U
    rfl
  · intro ρ hρ
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact eq_of_heq (hρ V.unop.1 V.unop.2)

/-- The actual levelwise constant-section map on sequence rings.
Source: Stacks 0941 and 0H7J (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceRing {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSequenceRing_existsUnique l E f).exists.choose

private theorem pullbackTensorSequenceRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = integralComparisonSequenceRingMap l E f := by
  apply (pullbackTensorSequenceRing_existsUnique l E f).unique
  · exact (pullbackTensorSequenceRing_existsUnique l E f).exists.choose_spec
  · intro n U
    rfl

/-- Module direct image on the ringed sequence site, with the actual coefficient action.
Source: Stacks 03D1 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{u + 1} (F := pullbackTensorSequenceBase f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight (pullbackTensorSequenceRing l E f).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Module Kan extension followed by sheafification is left adjoint to this direct image.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: pass to a small model in coefficient universe u + 1. The free module
presheaf presentation constructs inverse image with extension of scalars;
module sheafification gives its adjunction. Transport back to the stated
sequence sites. The right adjoint and its coefficient map are the displayed ones. -/
@[instance] theorem pullbackTensorSequenceDirect_rightAdjoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (pullbackTensorSequenceDirect l E f).IsRightAdjoint := by
  unfold pullbackTensorSequenceDirect
  rw [pullbackTensorSequenceRing_eq]
  exact integralComparisonSequenceDirectImage_isRightAdjoint l E f

/-- Canonical module inverse image on coefficient systems, retaining its adjunction.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceInverse {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSequenceDirect l E f).leftAdjoint

/-- The defining sequence-module adjunction, including its unit.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f ⊣ pullbackTensorSequenceDirect l E f :=
  Adjunction.ofIsRightAdjoint _

/-- Sequence inverse image is additive and exact, without a boundedness restriction.
Source: Stacks 03D2, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: on every vertical slice the ring map is the constant-ring comparison,
so inverse image is the exact ordinary constant-coefficient inverse image.
Kernels and cokernels of sequence modules are levelwise, giving exactness.
The additive adjunction criterion gives additivity. -/
theorem pullbackTensorSequenceInverse_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceInverse l E f).Additive ∧
      PreservesFiniteLimits (pullbackTensorSequenceInverse l E f) ∧
      PreservesFiniteColimits (pullbackTensorSequenceInverse l E f) := by
  simpa only [pullbackTensorSequenceInverse, pullbackTensorSequenceDirect,
    pullbackTensorSequenceRing_eq, integralComparisonSequencePullback,
    integralComparisonSequenceDirectImage, pullbackTensorSequenceBase,
    integralComparisonSequenceBaseChange] using
    integralComparisonSequencePullback_exact l E f

/-- The additive structure of sequence inverse image.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorSequenceInverse_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceInverse l E f).Additive :=
  (pullbackTensorSequenceInverse_exact l E f).1

/-- Finite-limit preservation of sequence inverse image.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorSequenceInverse_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (pullbackTensorSequenceInverse l E f) :=
  (pullbackTensorSequenceInverse_exact l E f).2.1

/-- Finite-colimit preservation of sequence inverse image.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorSequenceInverse_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullbackTensorSequenceInverse l E f) :=
  (pullbackTensorSequenceInverse_exact l E f).2.2

/-- The unbounded derived inverse image on the coherent sequence category itself.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (pullbackTensorSequenceInverse l E f).mapDerivedCategory

/-- The ordinary inverse limit of a coefficient system with its completed scalar action.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorOrdinaryLimit (W : Scheme.{u}) :
    coefficientSequenceModules l E W ⥤ integralTowerModules l E W :=
  coefficientSequenceRestriction l E W ⋙ lim

/-- Ordinary coherent reduction is left adjoint to the specified ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: send a completed module P to the system of its actual quotients
B_n tensor P. The quotient units form a map P to the limit after scalar
restriction. A system map from these quotients is equivalent, by the ordinary
scalar-extension adjunctions and their compatibility, to a map P to that limit.
This is the required natural Hom bijection. -/
@[instance] theorem pullbackTensorOrdinaryLimit_rightAdjoint (W : Scheme.{u}) :
    (pullbackTensorOrdinaryLimit l E W).IsRightAdjoint := by
  sorry

/-- Ordinary coherent reduction, fixed by its adjunction to the ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorOrdinaryReduction (W : Scheme.{u}) :=
  (pullbackTensorOrdinaryLimit l E W).leftAdjoint

/-- The ordinary reduction/limit adjunction and its canonical quotient units.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorOrdinaryAdjunction (W : Scheme.{u}) :
    pullbackTensorOrdinaryReduction l E W ⊣ pullbackTensorOrdinaryLimit l E W :=
  Adjunction.ofIsRightAdjoint _

/-- Additivity of ordinary coherent reduction and ordinary limit.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: restriction, limits and the scalar quotient functors are additive.
Alternatively use the additive-adjunction criterion for the displayed adjunction. -/
theorem pullbackTensorOrdinary_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryReduction l E W).Additive ∧
      (pullbackTensorOrdinaryLimit l E W).Additive := by
  have : (pullbackTensorOrdinaryLimit l E W).Additive := by
    have := coefficientConstantTowerLimitAdditive l E W
    change (coefficientSequenceRestriction l E W ⋙ lim).Additive
    infer_instance
  exact ⟨(pullbackTensorOrdinaryAdjunction l E W).left_adjoint_additive, inferInstance⟩

/-- The additive structure on ordinary coherent reduction.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorOrdinaryReduction_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryReduction l E W).Additive :=
  (pullbackTensorOrdinary_additive l E W).1

/-- The additive structure on the ordinary limit with completed coefficients.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorOrdinaryLimit_additive (W : Scheme.{u}) :
    (pullbackTensorOrdinaryLimit l E W).Additive :=
  (pullbackTensorOrdinary_additive l E W).2

/-- The ordinary limit with its completed-module source recorded explicitly.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorConstantLimit (W : Scheme.{u}) :
    (ℕᵒᵖ ⥤ integralTowerModules l E W) ⥤ integralTowerModules l E W := lim

/-- The additive structure of the explicitly typed constant-tower limit.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorConstantLimit_additive (W : Scheme.{u}) :
    (pullbackTensorConstantLimit l E W).Additive :=
  coefficientConstantTowerLimitAdditive l E W

/-- The standard derived localization instance for the completed-module tower category.
Source: Stacks 05RU (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorTowerHasDerived (W : Scheme.{u}) :
    HasDerivedCategory (ℕᵒᵖ ⥤ integralTowerModules l E W) := HasDerivedCategory.standard _

/-- The additive finite inverse-image functor with both size parameters fixed.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorLevelAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E f n).Additive :=
  integralOperationsLevelPullback_additive l E f n

/-- K-injective resolutions in the explicitly sized tower category.
Source: Stacks 079P and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorTowerKInjectives (W : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ integralTowerModules l E W) :=
  coefficientConstantTowers_haveKInjectives l E W

/-- The standard localization functor for completed-coefficient towers.
Source: Stacks 05RU (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorTowerQ (W : Scheme.{u}) :=
  @DerivedCategory.Q (ℕᵒᵖ ⥤ integralTowerModules l E W) _ _ (HasDerivedCategory.standard _)

/-- The canonical comparison from ordinary limit to the already specified total limit.
Source: Stacks 0941 and 08TC (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorLimitUnit (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    DerivedCategory.Q.obj
        (((pullbackTensorOrdinaryLimit l E W).mapHomologicalComplex (.up ℤ)).obj C) ⟶
      (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) :=
  letI := pullbackTensorConstantLimit_additive l E W
  DerivedCategory.Q.map
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (coefficientSequenceRestriction l E W ⋙
        (pullbackTensorConstantLimit l E W)))
      (.up ℤ)).inv.app C) ≫
  (pullbackTensorConstantLimit l E W).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
  (coefficientConstantTowerLimit l E W).map
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app C)

/-- On flat K-flat complexes the adjunction mate of the ordinary quotient unit
is the canonical comparison with coherent derived reduction. The formula takes
place in the system derived category, before evaluation.
Source: Stacks 0941, 07A6 and 09T5 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: ordinary reduction is tensor extension to the sequence ring. Flat K-flat
complexes compute its left derived functor. Derive the ordinary reduction/limit
adjunction using its ordinary quotient unit and the displayed total-limit unit.
Uniqueness of a left adjoint to coefficientSequenceLimit identifies this derived
adjunction with the recorded one. Its transpose is precisely the displayed
formula, which determines each component and hence the natural isomorphism. -/
theorem pullbackTensorReductionModel_existsUnique (W : Scheme.{u}) :
    ∃! e : integralOperationsGoodLocalization l E W ⋙
        (pullbackTensorCalculus l E W).reduction ≅
      (integralOperationsGoodComplex l E W).ι ⋙
        (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q,
      ∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
        ((pullbackTensorCalculus l E W).adjunction.homEquiv
          (DerivedCategory.Q.obj P.obj)
          (DerivedCategory.Q.obj
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
              P.obj))) (e.hom.app P) =
        DerivedCategory.Q.map
          (((pullbackTensorOrdinaryAdjunction l E W).mapHomologicalComplex (.up ℤ)).unit.app
            P.obj) ≫
          pullbackTensorLimitUnit l E W
            (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj
              P.obj) := by
  sorry

/-- The uniquely adjunction-normalized coherent reduction model.
Source: Stacks 0941 and 09T5 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReductionModel (W : Scheme.{u}) :=
  (pullbackTensorReductionModel_existsUnique l E W).exists.choose

/-- The ordinary scalar-extension adjunction of the actual finite reduction.
Source: Stacks 06YY (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorFiniteAdjunction (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralReductionFunctor l E W n ⊣ scalarReductionRestriction l E W n :=
  (scalarReductionExtension_adjunction l E W n).choose

/-- Evaluation of ordinary coherent reduction is the actual quotient extension,
with its adjunction unit rather than a chosen component map.
Source: Stacks 0941 and 06YY (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: take the adjoint of the ordinary reduction/limit unit followed by its
nth limit projection. The scalar-extension adjunction identifies this map with
B_n tensor P to the nth coherent quotient. The section formula sends 1 tensor x
to 1 tensor x, giving an isomorphism. Naturality follows from the two adjunctions;
the displayed transpose determines all components uniquely. -/
theorem pullbackTensorReductionEvaluation_existsUnique (W : Scheme.{u}) (n : ℕ) :
    ∃! e : unrestrictedIntegralReductionFunctor l E W n ≅
      pullbackTensorOrdinaryReduction l E W ⋙ coefficientSequenceEvaluation l E W n,
      ∀ M : integralTowerModules l E W,
        (pullbackTensorFiniteAdjunction l E W n).homEquiv M _ (e.hom.app M) =
          (pullbackTensorOrdinaryAdjunction l E W).unit.app M ≫
            limit.π ((coefficientSequenceRestriction l E W).obj
              ((pullbackTensorOrdinaryReduction l E W).obj M)) (op n) ≫
            (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
              ((pullbackTensorOrdinaryReduction l E W).obj M) := by
  sorry

/-- The unit-normalized quotient evaluation isomorphism.
Source: Stacks 0941 and 06YY (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReductionEvaluation (W : Scheme.{u}) (n : ℕ) :=
  (pullbackTensorReductionEvaluation_existsUnique l E W n).exists.choose

/-- Direct image on sequences commutes with evaluation by the identity on sections.
Source: Stacks 03D1 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: both functors evaluate M at (n, f-basechange U) with scalar action through
the same constant-section coefficient map. The identity section maps give the
natural isomorphism. Sectionwise extensionality proves uniqueness. -/
theorem pullbackTensorSequenceDirectEvaluation_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDirect l E f ⋙ coefficientSequenceEvaluation l E Y n ≅
      coefficientSequenceEvaluation l E X n ⋙
        coefficientProEtaleModuleDirectImage.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))),
      ∀ (M : coefficientSequenceModules l E X) (U : Y.ProEt)
        (x : ((coefficientSequenceEvaluation l E Y n).obj
          ((pullbackTensorSequenceDirect l E f).obj M)).val.obj (op U)),
        HEq ((e.hom.app M).val.app (op U) x) x := by
  sorry

/-- The sectionwise direct-image/evaluation comparison.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorSequenceDirectEvaluation_existsUnique l E f n).exists.choose

/-- The inverse-image/evaluation comparison is the adjunction mate of the
sectionwise direct-image comparison.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: transpose the displayed map under the finite module adjunction. The two
inverse-image functors are computed levelwise, so the resulting natural map is
invertible. The adjunction Hom bijection fixes its components and proves uniqueness. -/
theorem pullbackTensorSequenceInverseEvaluation_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! e : coefficientSequenceEvaluation l E Y n ⋙
        integralOperationsLevelPullback l E f n ≅
      pullbackTensorSequenceInverse l E f ⋙ coefficientSequenceEvaluation l E X n,
      ∀ M : coefficientSequenceModules l E Y,
        (coefficientProEtaleModuleAdjunction.{u, u} f
          (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).homEquiv
            ((coefficientSequenceEvaluation l E Y n).obj M) _ (e.hom.app M) =
          (coefficientSequenceEvaluation l E Y n).map
            ((pullbackTensorSequenceAdjunction l E f).unit.app M) ≫
          (pullbackTensorSequenceDirectEvaluation l E f n).hom.app
            ((pullbackTensorSequenceInverse l E f).obj M) := by
  sorry

/-- The canonical mate comparing sequence inverse image with finite inverse image.
Source: Stacks 03D2 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceInverseEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorSequenceInverseEvaluation_existsUnique l E f n).exists.choose

/-- Reordering a restricted sequence complex into a tower preserves its finite slices.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorRestrictedLevel (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)).obj
        (op n)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) :=
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceRestriction l E W ⋙
      (evaluation ℕᵒᵖ (integralTowerModules l E W)).obj (op n))) (.up ℤ)).app C ≪≫
  (NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).app C ≪≫
  ((Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceEvaluation l E W n ⋙
      scalarReductionRestriction l E W n)) (.up ℤ)).app C).symm

/-- The actual complex-to-tower reordering after completed scalar restriction.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorRestrictedTower (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

/-- The canonical augmentation of the ordinary inverse limit into its strict Roos model.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorRoosAugmentation (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    ((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
        ∏ᶜ (fun n : ℕ ↦
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n)) :=
  Pi.lift (fun n ↦ (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app P)

/-- The strict limit projections give a zero homotopy for the Roos augmentation.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: after every product projection the composite with 1-s is the difference
of consecutive compatible limit projections. It vanishes. The zero cochain has
zero differential, which is the displayed mapping-cocone lifting condition. -/
theorem pullbackTensorRoosAugmentation_condition (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain
        (((pullbackTensorConstantLimit l E W).mapHomologicalComplex (.up ℤ)).obj P)
        (∏ᶜ fun n : ℕ ↦
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n)) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (pullbackTensorRoosAugmentation l E W P ≫
          towerTransitionEndomorphism
            (K := fun n : ℕ ↦
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
            (integralOperationsTowerStep
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P))) = 0 := by
  have hz : pullbackTensorRoosAugmentation l E W P ≫
      towerTransitionEndomorphism
        (K := fun n : ℕ ↦
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
        (integralOperationsTowerStep
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P)) = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [towerTransitionEndomorphism, Preadditive.comp_sub, Preadditive.sub_comp,
      Category.comp_id,
      towerProductShift, Category.assoc, Pi.lift_π_assoc, pullbackTensorRoosAugmentation,
      Pi.lift_π, zero_comp]
    apply sub_eq_zero.mpr
    apply HomologicalComplex.hom_ext
    intro k
    exact (limit.w (P.X k) (homOfLE (Nat.le_succ n)).op).symm
  simp [hz]

/-- The specified (limit-projections, zero) chain map into Cone(1-s)[-1].
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorRoosUnit (W : Scheme.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) :=
  CochainComplex.mappingCocone.lift
    (towerTransitionEndomorphism
      (K := fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P).obj (op n))
      (integralOperationsTowerStep
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj P)))
    (pullbackTensorRoosAugmentation l E W P) 0
    (pullbackTensorRoosAugmentation_condition l E W P)

/-- The canonical total-limit/Roos isomorphism is fixed on K-injectives by the
actual right-derived comparison and the specified zero-homotopy augmentation.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: exact products identify the Roos construction with the total derived
limit. For a K-injective tower the ordinary limit computes that derived limit;
the displayed formula fixes the comparison there. Resolve any tower complex
by a K-injective one. Naturality and invertibility on quasi-isomorphisms extend
this formula uniquely, giving the natural isomorphism on all tower complexes. -/
theorem pullbackTensorRoosModel_existsUnique (W : Scheme.{u}) :
    ∃! e : pullbackTensorTowerQ l E W ⋙ coefficientConstantTowerLimit l E W ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ integralTowerModules l E W) ℤ) [I.IsKInjective],
        e.hom.app I =
          (Functor.rightDerivedFunctorObjQIso
            (pullbackTensorConstantLimit l E W) I).hom ≫
          DerivedCategory.Q.map (pullbackTensorRoosUnit l E W I) := by
  sorry

/-- The uniquely normalized total-limit/Roos model, including both cone coordinates.
Source: Stacks 08TC (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorRoosModel (W : Scheme.{u}) :=
  (pullbackTensorRoosModel_existsUnique l E W).exists.choose

/-- The ordinary quotient evaluation comparison on cochain complexes.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReductionEvaluationComplex (W : Scheme.{u}) (n : ℕ) :
    unrestrictedIntegralFiniteComplex l E W n ≅
      (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ) ⋙
        (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (pullbackTensorReductionEvaluation l E W n) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (pullbackTensorOrdinaryReduction l E W ⋙
        coefficientSequenceEvaluation l E W n)) (.up ℤ)).symm

/-- The unit-normalized inverse-image evaluation comparison on cochain complexes.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorInverseEvaluationComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    letI := integralOperationsLevelPullback_additive l E f n
    (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ) ⋙
      (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) ≅
    (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ) :=
  letI := integralOperationsLevelPullback_additive l E f n
  letI := pullbackTensorSequenceInverse_additive l E f
  letI := coefficientSequenceEvaluation_additive l E X n
  letI := coefficientSequenceEvaluation_additive l E Y n
  Functor.mapHomologicalComplexCompIso
    (Iso.refl (coefficientSequenceEvaluation l E Y n ⋙
      integralOperationsLevelPullback l E f n)) (.up ℤ) ≪≫
  NatIso.mapHomologicalComplex (pullbackTensorSequenceInverseEvaluation l E f n) (.up ℤ) ≪≫
  (Functor.mapHomologicalComplexCompIso
    (Iso.refl (pullbackTensorSequenceInverse l E f ⋙
      coefficientSequenceEvaluation l E X n)) (.up ℤ)).symm

/-- Each slice of the coherent pullback model is the recorded strict finite pullback.
Source: Stacks 0941 and 099N (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorPullbackTowerLevel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) :
    (pullbackTensorRestrictedTower l E X
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P))).obj
          (op n) ≅
      ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n) :=
  pullbackTensorRestrictedLevel l E X _ n ≪≫
  ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).mapIso
    ((pullbackTensorInverseEvaluationComplex l E f n).app
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
  ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).mapIso
    (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).mapIso
      ((pullbackTensorReductionEvaluationComplex l E Y n).app P).symm)

/-- The slice comparisons form one strict tower isomorphism, fixed at every level.
Source: Stacks 0941 and 099N (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: the quotient maps and inverse-image maps were fixed by their ordinary
adjunction units. Apply the two adjunction Hom bijections: both composites
across a quotient transition become the same quotient unit. Thus the level
comparisons commute strictly with transitions. They form a tower isomorphism;
its prescribed components give uniqueness by natural-transformation extensionality. -/
theorem pullbackTensorPullbackTower_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    ∃! e : pullbackTensorRestrictedTower l E X
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj
        (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P)) ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P,
      ∀ n : ℕ, e.app (op n) = pullbackTensorPullbackTowerLevel l E f P n := by
  sorry

/-- The unit-normalized strict pullback tower comparison.
Source: Stacks 0941 and 099N (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorPullbackTower {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :=
  (pullbackTensorPullbackTower_existsUnique l E f P).exists.choose

/-- Each coherent tensor slice is the recorded strict finite total tensor.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorTensorTowerLevel (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) :
    (pullbackTensorRestrictedTower l E W
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q)))).obj
            (op n) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P,Q)).obj (op n) :=
  pullbackTensorRestrictedLevel l E W _ n ≪≫
  ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
    (coefficientEvaluationTensorIso l E W n _ _) ≪≫
  ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
    ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n)).mapIso
        (Iso.prod ((pullbackTensorReductionEvaluationComplex l E W n).app P).symm
          ((pullbackTensorReductionEvaluationComplex l E W n).app Q).symm))

/-- The tensor slice comparisons form a strict system map with the actual quotient maps.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: the reduction comparisons preserve scalar-extension units and the evaluation
tensor map sends pure tensors to their two evaluated factors. Across every quotient
transition both routes send x tensor y to its two reduced factors. Tensor generators,
sheafification and total-summand injections give strict equality. The displayed
components therefore define a tower isomorphism and determine it uniquely. -/
theorem pullbackTensorTensorTower_existsUnique (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    ∃! e : pullbackTensorRestrictedTower l E W
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj
        ((((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P),
          (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q))) ≅
      (integralOperationsTensorTowerFunctor l E W).obj (P,Q),
      ∀ n : ℕ, e.app (op n) = pullbackTensorTensorTowerLevel l E W P Q n := by
  sorry

/-- The uniquely prescribed strict tensor tower comparison.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorTensorTower (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose

/-- The total limit of a coherent complex, normalized by the actual Roos model.
Source: Stacks 08TC and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorLimitRoos (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos (pullbackTensorRestrictedTower l E W C)) :=
  (coefficientConstantTowerLimit l E W).mapIso
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
  (pullbackTensorRoosModel l E W).app
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

/-- Pullback in the coherent reduction/limit presentation, before restricting objects.
Source: Stacks 0941, 099N (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReferencePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f ⋙
    coefficientSequenceLimit l E X

/-- Completed tensor in the coherent reduction/limit presentation.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReferenceTensor (W : Scheme.{u}) :=
  ((pullbackTensorCalculus l E W).reduction.prod
    (pullbackTensorCalculus l E W).reduction) ⋙
      (pullbackTensorCalculus l E W).systemClosed.tensor ⋙ coefficientSequenceLimit l E W

/-- The coherent pullback presentation computes the actual strict finite-pullback Roos model.
Source: Stacks 08TC, 0941, 099N (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReferencePullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (pullbackTensorReferencePullback l E f).obj (DerivedCategory.Q.obj P.obj) ≅
      (integralOperationsPullbackOnGood l E f).obj P :=
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorSequenceDerived l E f).mapIso
      ((pullbackTensorReductionModel l E Y).app P)) ≪≫
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.app
      (((pullbackTensorOrdinaryReduction l E Y).mapHomologicalComplex (.up ℤ)).obj P.obj)) ≪≫
  pullbackTensorLimitRoos l E X _ ≪≫
  DerivedCategory.Q.mapIso
    (integralOperationsRoosFunctor.mapIso (pullbackTensorPullbackTower l E f P.obj))

/-- The actual integral pullback is identified with coherent reduction and limit
by equality with its full strict Roos comparison on every good representative.
Source: Stacks 08TC, 0941, 099N (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: the preceding model is a composition of the adjunction-normalized coherent
reduction comparison, exact pullback factorization, the right-derived Roos model,
and the unit-normalized strict tower isomorphism. Thus its representative functor
is exactly integralOperationsPullbackOnGood. Compare the two descents of that
functor. The localization universal property gives the stated unique isomorphism. -/
theorem pullbackTensorIntegralPullbackModel_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : integralDerivedPullback l E f ≅ pullbackTensorReferencePullback l E f,
      ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        e.app (DerivedCategory.Q.obj P.obj) =
          (integralDerivedPullbackComparison l E f).app P ≪≫
            (pullbackTensorReferencePullbackModel l E f P).symm := by
  sorry

/-- The uniquely Roos-normalized integral pullback realization.
Source: Stacks 08TC, 0941, 099N (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorIntegralPullbackModel {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorIntegralPullbackModel_existsUnique l E f).exists.choose

/-- Ordinary coherent reduction preserves K-flat representatives.
Source: Stacks 06YY and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: extension to the sequence ring preserves K-flatness by the tensor/restriction
adjunction, since restriction preserves acyclic complexes. Apply the independent
coefficient characterization at the explicitly sized sequence site. -/
theorem pullbackTensorReductionGood (W : Scheme.{u})
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
      (pullbackTensorSequenceSmall W)
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)
      (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P.obj) := by
  sorry

/-- The recorded system tensor model, at the actual sequence-site universes.
Source: Stacks 06YU (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSystemModel (W : Scheme.{u})
    (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
      (pullbackTensorSequenceSmall W) (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × W.ProEt) (inferInstance : Category.{u} (ℕ × W.ProEt))
      (pullbackTensorSequenceSmall W) (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) Q) :=
  CoefficientTensorModels.iso.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W) (pullbackTensorCalculus l E W).systemClosed
    (pullbackTensorCalculus l E W).systemTensorModel P Q hP hQ

/-- The reference tensor computes the prescribed full strict tensor tower.
Source: Stacks 08TC, 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReferenceTensorModel (W : Scheme.{u})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (pullbackTensorReferenceTensor l E W).obj
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≅
      (integralOperationsTensorOnGood l E W).obj (P,Q) :=
  (coefficientSequenceLimit l E W).mapIso
    ((pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
      (Iso.prod ((pullbackTensorReductionModel l E W).app P)
        ((pullbackTensorReductionModel l E W).app Q))) ≪≫
  (coefficientSequenceLimit l E W).mapIso
    (pullbackTensorSystemModel l E W _ _
      (pullbackTensorReductionGood l E W P) (pullbackTensorReductionGood l E W Q)).symm ≪≫
  pullbackTensorLimitRoos l E W _ ≪≫
  DerivedCategory.Q.mapIso
    (integralOperationsRoosFunctor.mapIso (pullbackTensorTensorTower l E W P.obj Q.obj))

/-- The integral tensor realization is fixed by its complete strict Roos model.
Source: Stacks 08TC and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: both functors descend integralOperationsTensorOnGood. The preceding
comparison identifies the whole tower and the Roos differential, not just its
finite projections. The localization universal property gives a unique natural
isomorphism compatible with these specified comparison components. -/
theorem pullbackTensorIntegralTensorModel_existsUnique (W : Scheme.{u}) :
    ∃! e : integralCompletedTensor l E W ≅ pullbackTensorReferenceTensor l E W,
      ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
        e.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
          (integralCompletedTensorComparison l E W).app (P,Q) ≪≫
            (pullbackTensorReferenceTensorModel l E W P Q).symm := by
  sorry

/-- The uniquely Roos-normalized tensor realization.
Source: Stacks 08TC and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorIntegralTensorModel (W : Scheme.{u}) :=
  (pullbackTensorIntegralTensorModel_existsUnique l E W).exists.choose

/-- The ordinary tensor comparison on coherent complexes is determined on every
pure-tensor total summand by the actual inverse-image adjunction unit.
Source: Stacks 03EL and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: use the ordinary ringed-topos pullback/tensor comparison on each pair of
terms. Its pure-tensor formula is the displayed unit equation. Totalization
respects both differential summands. Tensor generators and total-summand
injections prove uniqueness; the ordinary inverse gives invertibility. -/
theorem pullbackTensorSequenceCochain_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) ⋙
        (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ) ≅
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).prod
        ((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X),
      ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
        (p q k : ℤ) (h : p + q = k) (V : ℕ × Y.ProEt)
        (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
        ((e.hom.app (P,Q)).f k).val.app
          (op ((pullbackTensorSequenceBase f).obj V))
          (((pullbackTensorSequenceAdjunction l E f).unit.app
            (((coefficientTotalTensor.{u, u + 1, u}
              (coefficientSequenceTopology (ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app (op V)
            (coefficientTensorGenerator.{u, u + 1, u}
              (coefficientSequenceTopology (ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y) P Q p q k h (op V) x y)) =
        coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h (op ((pullbackTensorSequenceBase f).obj V))
          (((pullbackTensorSequenceAdjunction l E f).unit.app (P.X p)).val.app (op V) x)
          (((pullbackTensorSequenceAdjunction l E f).unit.app (Q.X q)).val.app (op V) y) := by
  sorry

/-- The pure-tensor normalized comparison of strict coherent complexes.
Source: Stacks 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSequenceCochain {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSequenceCochain_existsUnique l E f).exists.choose

/-- Exact sequence inverse image preserves K-flatness.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: tensor commutes with inverse image by the preceding ordinary comparison.
The right adjoint and exact constant-coefficient pullback identify the relevant
acyclic tests; equivalently check the flat tensor filtration termwise and use
K-flat resolutions. This proves the independent-coefficient criterion. -/
theorem pullbackTensorSequenceGood {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × X.ProEt) (inferInstance : Category.{u} (ℕ × X.ProEt))
      (pullbackTensorSequenceSmall X) (coefficientSequenceTopology (ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
      (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- The derived coherent comparison is uniquely fixed before applying Rlim.
Source: Stacks 06YU, 07A4 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: restrict the pure-tensor cochain comparison to K-flat pairs. Exact inverse
image preserves these pairs. The displayed square is the localization descent
square with the prescribed tensor and pullback models. The K-flat resolving
localization gives existence and uniqueness, including all system transitions. -/
theorem pullbackTensorSystemComparison_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        pullbackTensorSequenceDerived l E f ≅
      ((pullbackTensorSequenceDerived l E f).prod (pullbackTensorSequenceDerived l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor,
      ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
        (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
          (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) P)
        (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
          (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y) Q),
        (pullbackTensorSequenceDerived l E f).map
          (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
              ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) =
        (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app (P,Q)) ≫
          (pullbackTensorSystemModel l E X _ _
            (pullbackTensorSequenceGood l E f P hP)
            (pullbackTensorSequenceGood l E f Q hQ)).hom := by
  sorry

/-- The canonical comparison as a map of coherent derived systems.
Source: Stacks 07A4 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorSystemComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullbackTensorSystemComparison_existsUnique l E f).exists.choose

/-- The systems used in the integral comparison are normalized, so the actual
reduction/limit counits on them are invertible.
Source: Stacks 0941; Bhatt--Scholze 3.4.12 (blueprint:
def-pur-completed-pullback-tensor-comparison).
Proof: the reduction systems of constructible inputs are normalized. Tensor and
constant-coefficient inverse image preserve the Cartesian quotient comparisons
by their flat K-flat models, including ramified transitions. The normalized DVR
effectivity theorem identifies the displayed counits as equivalences. -/
theorem pullbackTensorComparisonCounits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [_hX : ∀ x : X, Invertible (l : X.residueField x)]
    [_hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    IsIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
          (pullbackTensorCalculus l E Y).reduction.obj N.obj))) ∧
    IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
      ((pullbackTensorSequenceDerived l E f).obj
        ((pullbackTensorCalculus l E Y).reduction.obj M.obj))) ∧
    IsIso ((pullbackTensorCalculus l E X).adjunction.counit.app
      ((pullbackTensorSequenceDerived l E f).obj
        ((pullbackTensorCalculus l E Y).reduction.obj N.obj))) := by
  sorry

/-- The integral comparison in coherent coordinates is exactly Rlim of the
canonical system comparison, conjugated only by the specified coherent counits.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorReferenceComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorReferencePullback l E f).obj
      ((pullbackTensorReferenceTensor l E Y).obj (M.obj,N.obj)) ≅
    (pullbackTensorReferenceTensor l E X).obj
      ((pullbackTensorReferencePullback l E f).obj M.obj,
        (pullbackTensorReferencePullback l E f).obj N.obj) :=
  letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).1
  letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).2.1
  letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).2.2
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorSequenceDerived l E f).mapIso
      (asIso ((pullbackTensorCalculus l E Y).adjunction.counit.app
        ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj
          ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
            (pullbackTensorCalculus l E Y).reduction.obj N.obj))))) ≪≫
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorSystemComparison l E f).app
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
        (pullbackTensorCalculus l E Y).reduction.obj N.obj)) ≪≫
  (coefficientSequenceLimit l E X).mapIso
    ((pullbackTensorCalculus l E X).systemClosed.tensor.mapIso
      (Iso.prod
        (asIso ((pullbackTensorCalculus l E X).adjunction.counit.app
          ((pullbackTensorSequenceDerived l E f).obj
            ((pullbackTensorCalculus l E Y).reduction.obj M.obj)))).symm
        (asIso ((pullbackTensorCalculus l E X).adjunction.counit.app
          ((pullbackTensorSequenceDerived l E f).obj
            ((pullbackTensorCalculus l E Y).reduction.obj N.obj)))).symm))

/-- The canonical completed integral comparison, transported from the actual
coherent-system Rlim map to the recorded completed operations and their full
constructible subcategories.
Source: Stacks 07A4 and 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def canonicalIntegralPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@IntegralPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  ObjectProperty.isoMk _
    ((pullbackTensorIntegralPullbackModel l E f).app
        ((integralCompletedTensor l E Y).obj (M.obj,N.obj)) ≪≫
      (pullbackTensorReferencePullback l E f).mapIso
        ((pullbackTensorIntegralTensorModel l E Y).app (M.obj,N.obj)) ≪≫
      (@pullbackTensorReferenceComparison l _ E _ _ _ X Y f hX hY) M N ≪≫
      (pullbackTensorReferenceTensor l E X).mapIso
        (Iso.prod ((pullbackTensorIntegralPullbackModel l E f).app M.obj).symm
          ((pullbackTensorIntegralPullbackModel l E f).app N.obj).symm) ≪≫
      ((pullbackTensorIntegralTensorModel l E X).app
        ((integralDerivedPullback l E f).obj M.obj,
          (integralDerivedPullback l E f).obj N.obj)).symm)


/-- The finite inverse image in the strict integral tower is the intrinsic inverse
image, with equality on the actual adjunction-unit sections.
Source: Stacks 00YV, 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: both right adjoints take sections over the same base-change object with
the same constant coefficient action. The identity of right adjoints induces
this comparison of left adjoints. Its unit formula characterizes it uniquely. -/
theorem pullbackTensorLevelIntrinsic_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : integralOperationsLevelPullback l E f n ≅
      sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y n) (U : Y.ProEt)
        (x : M.val.obj (op U)),
        (e.hom.app M).val.app (op ((proEtaleBaseChange f).obj U))
          (((coefficientProEtaleModuleAdjunction.{u, u} f
            (CommRingCat.of (ULift.{u + 1}
              (finiteCoefficientRing l E (n + 1))))).unit.app M).val.app (op U) x) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op U) x := by
  let A := finiteCoefficientRing l E (n + 1)
  let adj₁ := coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1} A))
  let adj₂ : sfIntrinsicPullback A f ⊣
      coefficientProEtaleModuleDirectImage.{u, u} f
        (CommRingCat.of (ULift.{u + 1} A)) :=
    sfIntrinsicConstantModuleAdjunction f A
  refine ⟨adj₁.leftAdjointUniq adj₂, ?_, ?_⟩
  · intro M U x
    exact congrArg (fun a ↦ a.val.app (op U) x)
      (Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ M)
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (adj₁.homEquiv M _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    ext U x
    exact he M U.unop x

/-- The unit-normalized realization of the finite pullback used by the strict tower.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorLevelIntrinsic {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose

/-- Evaluating the system inverse image gives the finite intrinsic inverse image;
the comparison is fixed on all cochain representatives by the two ordinary units.
Source: Stacks 0941, 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: apply the exact evaluation functor to a cochain representative. The
ordinary inverse-image/evaluation mate and the unit-normalized intrinsic
realization give the displayed chain comparison. Exact localization descends
it uniquely, since every derived object is represented by a complex. -/
theorem pullbackTensorDerivedEvaluation_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f,
      ∀ P : CochainComplex (coefficientSequenceModules l E Y) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app P) ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((pullbackTensorInverseEvaluationComplex l E f n).inv.app P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pullbackTensorLevelIntrinsic l E f n) (.up ℤ)).hom.app
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)) := by
  sorry

/-- The actual evaluation comparison, including its fixed cochain normalization.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorDerivedEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose

/-- The coherent comparison whose limit defines μI evaluates to the same μF at
EVERY finite level, under the canonical tensor and inverse-image comparisons.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: on a flat K-flat pair both routes are the totalization of the identical
ordinary section formula. The evaluation tensor comparison and inverse-image
comparison preserve these sections by their normalizations. K-flat descent
therefore proves the equation on arbitrary coherent derived inputs. -/
theorem pullbackTensorSystemComparison_evaluation {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : coefficientSequenceDerived l E Y) :
    (coefficientSequenceDerivedEvaluation l E X n).map
      ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
      ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
        ((pullbackTensorSequenceDerived l E f).obj M,
          (pullbackTensorSequenceDerived l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((pullbackTensorDerivedEvaluation l E f n).hom.app M)
          ((pullbackTensorDerivedEvaluation l E f n).hom.app N)) =
    (pullbackTensorDerivedEvaluation l E f n).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom := by
  sorry


/-- Associativity for the actual coherent μ whose derived limit is the integral μ.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: on three simultaneous flat K-flat representatives the two maps send
(x tensor y) tensor z to f*x tensor (f*y tensor f*z). The total reassociation
preserves the signed differential and all sequence restrictions. Localize this
equality of coherent complexes; applying the actual limit functor preserves it. -/
theorem pullbackTensorSystemComparison_associativity {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N P : coefficientSequenceDerived l E Y) :
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.associator M N P).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (M,(pullbackTensorCalculus l E Y).systemClosed.tensor.obj (N,P)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((pullbackTensorSystemComparison l E f).hom.app (N,P))) =
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N),P) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorSystemComparison l E f).hom.app (M,N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l E X).systemClosed.monoidal.associator
        ((pullbackTensorSequenceDerived l E f).obj M)
        ((pullbackTensorSequenceDerived l E f).obj N)
        ((pullbackTensorSequenceDerived l E f).obj P)).hom := by
  sorry

/-- Koszul braiding for the same coherent μ before taking its derived limit.
Source: Stacks 06YS, 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: both maps take a homogeneous generator x tensor y of degrees p,q to
(-1)^(pq) f*y tensor f*x. The equality respects every sequence restriction and
descends through the specified K-flat tensor models. Its image under the actual
limit, scalar localization, and common-stage maps gives the higher-level equation. -/
theorem pullbackTensorSystemComparison_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N : coefficientSequenceDerived l E Y) :
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y)
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel).hom.app (M,N)) ≫
      (pullbackTensorSystemComparison l E f).hom.app (N,M) =
    (pullbackTensorSystemComparison l E f).hom.app (M,N) ≫
      (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).systemTensorModel).hom.app
          ((pullbackTensorSequenceDerived l E f).obj M,
            (pullbackTensorSequenceDerived l E f).obj N) := by
  sorry

/-- Both unit equations for the coherent μ used to define the integral comparison.
Source: Stacks 03EL, 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: the inverse image of the sequence-ring unit maps to the target ring unit
by the given constant-section ring map. The tensor generator formulas give both
unit equations on complexes, compatibly with every restriction. Descend to
systems and apply the specified limit and scalar transports. -/
theorem pullbackTensorSystemComparison_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ ε : (pullbackTensorSequenceDerived l E f).obj
        (pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l E X).systemClosed.monoidal.tensorUnit,
      ∀ M : coefficientSequenceDerived l E Y,
        ((pullbackTensorSystemComparison l E f).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit,M) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.leftUnitor
            ((pullbackTensorSequenceDerived l E f).obj M)).hom =
        (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.leftUnitor M).hom) ∧
        ((pullbackTensorSystemComparison l E f).hom.app
          (M,(pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l E X).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((pullbackTensorCalculus l E X).systemClosed.monoidal.rightUnitor
            ((pullbackTensorSequenceDerived l E f).obj M)).hom =
        (pullbackTensorSequenceDerived l E f).map
          ((pullbackTensorCalculus l E Y).systemClosed.monoidal.rightUnitor M).hom) := by
  sorry

end CoherentSystems

section QuotientCompatibility
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Cache additive finite inverse image with the explicitly sized coefficient ring.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorFiniteAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
  sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f

/-- Cache the actual quotient extension's published additive structure.
Source: Stacks 06YY (blueprint: def-pur-completed-pullback-tensor-comparison). -/
instance pullbackTensorQuotientAdditive (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientExtension l E W h).Additive :=
  coefficientFiniteQuotientExtensionAdditive l E W h

/-- The quotient/pullback comparison preserves the two actual adjunction units.
Source: Stacks 06YY and 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: tensor association and constant inverse image identify the two ordinary
functors. Both iterated units send x to 1 tensor f*x. Their equality determines
the comparison on the generators of the two left adjoints, proving uniqueness. -/
theorem pullbackTensorQuotientOrdinary_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :
    ∃! e : sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h ≅
      coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f,
      ∀ (M : normalizedDVRModules l E Y m) (U : Y.ProEt)
        (x : M.val.obj (Opposite.op U)),
        (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (coefficientFiniteQuotientUnitSection l E X h
            ((sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f).obj M)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f
              (finiteCoefficientRing l E (m + 1))).unit.app M).val.app (Opposite.op U) x)) =
        ((sfIntrinsicConstantModuleAdjunction f
          (finiteCoefficientRing l E (n + 1))).unit.app
            ((coefficientFiniteQuotientExtension l E Y h).obj M)).val.app (Opposite.op U)
          (coefficientFiniteQuotientUnitSection l E Y h M (Opposite.op U) x) := by
  sorry

/-- The unit-normalized ordinary quotient/pullback comparison.
Source: Stacks 06YY and 03D2 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorQuotientOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :=
  (pullbackTensorQuotientOrdinary_existsUnique l E f h).exists.choose

/-- Finite constant-coefficient inverse image preserves K-flat complexes.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: use the constant-ring pullback/tensor comparison and exact inverse image.
Apply the K-flat criterion, or transport the recorded ringed pullback preservation
along the unit-normalized finite realization. No coefficient Tor-dimension is used. -/
theorem pullbackTensorFiniteGood {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y n) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
      (((sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

/-- The ordinary quotient/pullback comparison on complexes, with both composition
identifications and all additive instances supplied explicitly.
Source: Stacks 06YY, 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorQuotientComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    (sfIntrinsicPullback
      (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
    (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
      (sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ) := by
  letI := coefficientFiniteQuotientExtensionAdditive l E X h
  letI := coefficientFiniteQuotientExtensionAdditive l E Y h
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (m + 1)) f
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  exact Functor.mapHomologicalComplexCompIso
    (F := sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f)
    (G := coefficientFiniteQuotientExtension l E X h) (Iso.refl _) (.up ℤ) ≪≫
    NatIso.mapHomologicalComplex
      (F := sfIntrinsicPullback (finiteCoefficientRing l E (m + 1)) f ⋙
        coefficientFiniteQuotientExtension l E X h)
      (G := coefficientFiniteQuotientExtension l E Y h ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
      (pullbackTensorQuotientOrdinary l E f h) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := coefficientFiniteQuotientExtension l E Y h)
      (G := sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f)
      (Iso.refl _) (.up ℤ)).symm

/-- The quotient/pullback isomorphism is fixed by its full K-flat counit square.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: the preceding ordinary comparison on K-flat representatives identifies
the two derived functors. The universal quotient counit and exact-pullback
factorization give precisely this square. K-flat localization determines a
unique natural isomorphism from the displayed squares. -/
theorem pullbackTensorQuotient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f,
      ∀ (P : CochainComplex (normalizedDVRModules l E Y m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology Y) (R := integralCoefficientCommRingSheaf l E Y m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
          (finiteDerivedPullback l E n f).map
            (coefficientFiniteQuotientModel l E Y h P hP).hom ≫
          (sfIntrinsicPullback
            (finiteCoefficientRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app _ =
        (coefficientFiniteQuotientDerived l E X h).map
          ((sfIntrinsicPullback
            (finiteCoefficientRing l E (m + 1)) f).mapDerivedCategoryFactors.hom.app P) ≫
          (coefficientFiniteQuotientModel l E X h _
            (pullbackTensorFiniteGood l E f m P hP)).hom ≫
          DerivedCategory.Q.map ((pullbackTensorQuotientComplex l E f h).hom.app P) := by
  sorry

/-- The derived quotient/pullback comparison with its fixed K-flat normalization.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison). -/
def pullbackTensorQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (pullbackTensorQuotient_existsUnique l E f h).exists.choose

/-- The finite comparison commutes with every derived quotient B_m to B_n,
including m = n. All four change-of-coefficient arrows are the normalized ones.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: on a flat K-flat pair the two routes carry 1 tensor f*(x tensor y)
to f*(1 tensor x) tensor f*(1 tensor y). The quotient tensor comparison is
normalized on these same generators. Totalize and use the quotient counits
and K-flat localization to obtain the displayed derived equation. -/
theorem canonicalFinitePullbackTensor_quotient {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))) :
    (coefficientFiniteQuotientDerived l E X h).map
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f m hX hY) M N).hom ≫
      ((pullbackTensorCalculus l E X).quotientCalculus.tensor h).hom.app
        ((finiteDerivedPullback l E m f).obj M,(finiteDerivedPullback l E m f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((pullbackTensorQuotient l E f h).hom.app M)
          ((pullbackTensorQuotient l E f h).hom.app N)) =
    (pullbackTensorQuotient l E f h).hom.app
      ((finiteIntrinsicDerivedTensor l E Y m).obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).quotientCalculus.tensor h).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        ((coefficientFiniteQuotientDerived l E Y h).obj M)
        ((coefficientFiniteQuotientDerived l E Y h).obj N)).hom := by
  sorry
/-- The finite comparison commutes with every derived quotient B_m to B_n,
including m = n. All four change-of-coefficient arrows are the normalized ones.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: on a flat K-flat pair the two routes carry 1 tensor f*(x tensor y)
to f*(1 tensor x) tensor f*(1 tensor y). The quotient tensor comparison is
normalized on these same generators. Totalize and use the quotient counits
and K-flat localization to obtain the displayed derived equation. -/
def canonicalFinitePullbackTensor_quotient_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    {m n : ℕ} (h : n ≤ m)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))) :=
    (coefficientFiniteQuotientDerived l E X h).map
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f m hX hY) M N).hom ≫
      ((pullbackTensorCalculus l E X).quotientCalculus.tensor h).hom.app
        ((finiteDerivedPullback l E m f).obj M,(finiteDerivedPullback l E m f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((pullbackTensorQuotient l E f h).hom.app M)
          ((pullbackTensorQuotient l E f h).hom.app N)) =
    (pullbackTensorQuotient l E f h).hom.app
      ((finiteIntrinsicDerivedTensor l E Y m).obj (M,N)) ≫
      (finiteDerivedPullback l E n f).map
        (((pullbackTensorCalculus l E Y).quotientCalculus.tensor h).hom.app (M,N)) ≫
      ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
        ((coefficientFiniteQuotientDerived l E Y h).obj M)
        ((coefficientFiniteQuotientDerived l E Y h).obj N)).hom
end QuotientCompatibility

section LocalizationComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Rationalization fixes the comparison arrow itself, not just its isomorphism class.
Source: blueprint scalar localization paragraph (blueprint:
def-pur-completed-pullback-tensor-comparison).
Proof: apply the recorded localization functor to the integral comparison and its
inverse. Its object formula agrees with the rational operations. The localized
inverse identities make this an isomorphism; equality of homs determines it uniquely. -/
theorem canonicalRationalPullbackTensor_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj (((@rationalDerivedTensor l _ E
      _ _ _ Y hY)).obj (M,N)) ≅
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).obj
          (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M, ((@rationalDerivedPullback l
            _ E _ _ _ X Y f hX hY)).obj N),
      HEq e.hom ((sfRationalConstructibleLocalization l E X).map
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj).hom) := by
  let T (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :=
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
  let F := (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
  let e := (sfRationalConstructibleLocalization l E X).mapIso
    ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj)
  have hs : (rationalDerivedPullback l E f).obj
      ((rationalDerivedTensor l E Y).obj (M,N)) =
        (sfRationalConstructibleLocalization l E X).obj
          ((constructibleIntegralPullback l E f).obj
            ((constructibleIntegralTensor l E Y).obj (M.obj,N.obj))) := by
    dsimp only [rationalDerivedPullback, rationalDerivedTensor]
    rw [F, T Y (M,N)]
    rfl
  have ht : (rationalDerivedTensor l E X).obj
      ((rationalDerivedPullback l E f).obj M, (rationalDerivedPullback l E f).obj N) =
        (sfRationalConstructibleLocalization l E X).obj
          ((constructibleIntegralTensor l E X).obj
            ((constructibleIntegralPullback l E f).obj M.obj,
              (constructibleIntegralPullback l E f).obj N.obj)) := by
    dsimp only [rationalDerivedPullback, rationalDerivedTensor]
    rw [T X, F M, F N]
    rfl
  refine ⟨eqToIso hs ≪≫ e ≪≫ (eqToIso ht).symm, ?_, ?_⟩
  · apply (conj_eqToHom_iff_heq _ e.hom hs ht).mp
    rfl
  · intro e' he'
    apply Iso.ext
    apply eq_of_heq
    exact he'.trans ((conj_eqToHom_iff_heq _ e.hom hs ht).mp rfl).symm

/-- The localized canonical integral comparison.
Source: blueprint scalar localization paragraph (blueprint:
def-pur-completed-pullback-tensor-comparison). -/
def canonicalRationalPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@RationalPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  ((@canonicalRationalPullbackTensor_existsUnique l _ E _ _ _ X Y f hX hY) M N).exists.choose
end LocalizationComparison

section CommonComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The rational comparison in any common finite stage, with all four prescribed
pullback/tensor transition comparisons included.
Source: blueprint common-stage paragraph (blueprint: def-pur-completed-pullback-tensor-comparison).
-/
def pullbackTensorAtCommonStage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageTensorObject l Ω Y P Q).stage ≤ L) :
    (commonStagePullbackObject l Ω f (commonStageTensorObject l Ω Y P Q)).toStage h ≅
      (commonStageTensorObject l Ω X
        (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q)).toStage h :=
  commonStagePullbackComparison l Ω f (commonStageTensorObject l Ω Y P Q) L h ≪≫
  ((@rationalDerivedPullback l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X Y f
    hX hY)).mapIso
    (commonStageTensorComparison l Ω Y P Q L h) ≪≫
  (@canonicalRationalPullbackTensor l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _
    _ X Y f hX hY) _ _ ≪≫
  ((@rationalDerivedTensor l _ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
    hX)).mapIso
    (Iso.prod (commonStagePullbackComparison l Ω f P L
      (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)).symm
      (commonStagePullbackComparison l Ω f Q L
        (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)).symm) ≪≫
  (commonStageTensorComparison l Ω X
    (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q) L h).symm

/-- The algebraically closed comparison is the actual common-stage class at
EVERY larger finite coefficient stage, so enlargement and scalar extension are fixed.
Source: blueprint common-stage paragraph (blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: represent the comparison at the finite compositum by the preceding formula.
The rational scalar-extension square makes the same formula at any larger stage
the transition of that representative. The inverse formula gives the inverse
class. Every allowed stage therefore represents the same arrow. In particular
the compositum formula determines the arrow, hence determines the isomorphism uniquely. -/
theorem canonicalCommonStagePullbackTensor_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (P Q : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj
        (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (P,Q)) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).obj
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj P,
          ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj Q),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω Y P Q).stage ≤ L),
        HEq e.hom
          (ofHom (commonStagePullbackObject l Ω f (commonStageTensorObject l Ω Y P Q))
            (commonStageTensorObject l Ω X
              (commonStagePullbackObject l Ω f P) (commonStagePullbackObject l Ω f Q))
            L h h ((@pullbackTensorAtCommonStage l _ Ω _ _ _ X Y f hX hY) P Q L h).hom) := by
  sorry

/-- The stage-independent canonical comparison in the actual colimit Hom group.
Source: blueprint common-stage paragraph (blueprint: def-pur-completed-pullback-tensor-comparison).
-/
def canonicalCommonStagePullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@CommonStagePullbackTensorComparison l _ Ω _ _ _ X Y f hX hY) := fun P Q ↦
  ((@canonicalCommonStagePullbackTensor_existsUnique l _ Ω _ _ _ X Y f hX hY) P Q).exists.choose
end CommonComparison

section ScalarCompatibility
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Integral scalar extension commutes with the comparison arrow, including
ramified extensions, under the recorded canonical operation comparisons.
Source: blueprint scalar-extension paragraph; Stacks 0941 and 07A4
(blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: use one flat K-flat representative pair and the actual quotient models
for O_L/varpi_L^m. Both paths send b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The equality respects every quotient map;
apply the actual coherent-system limit and its normalized substitutions. -/
theorem canonicalIntegralPullbackTensor_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).map ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (integralTensorScalarComparison l E L ι X
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
      ((@constructibleIntegralTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom (integralPullbackScalarComparison l E L ι f M).hom
          (integralPullbackScalarComparison l E L ι f N).hom) =
    (integralPullbackScalarComparison l E L ι f
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
      ((@constructibleIntegralPullback l _ L _ _ _ X Y f hX hY)).map
        (integralTensorScalarComparison l E L ι Y M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj N)).hom := by
  sorry

/-- The rational scalar-extension square is the localized integral square.
Source: blueprint scalar-extension paragraph (blueprint:
def-pur-completed-pullback-tensor-comparison).
Proof: localize the preceding integral equality. Each operation comparison is
by definition the image of its integral component. Bilinearity then gives the
same square on every rational input, including identity scalar extensions. -/
theorem canonicalRationalPullbackTensor_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) :
    (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (rationalTensorScalarComparison l E L ι X).hom.app
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M,((@rationalDerivedPullback l _ E
          _ _ _ X Y f hX hY)).obj N) ≫
      ((@rationalDerivedTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom ((rationalPullbackScalarComparison l E L ι f).hom.app M)
          ((rationalPullbackScalarComparison l E L ι f).hom.app N)) =
    (rationalPullbackScalarComparison l E L ι f).hom.app
      (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) ≫
      ((@rationalDerivedPullback l _ L _ _ _ X Y f hX hY)).map
        ((rationalTensorScalarComparison l E L ι Y).hom.app (M,N)) ≫
      ((@canonicalRationalPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)).hom := by
  sorry
/-- Integral scalar extension commutes with the comparison arrow, including
ramified extensions, under the recorded canonical operation comparisons.
Source: blueprint scalar-extension paragraph; Stacks 0941 and 07A4
(blueprint: def-pur-completed-pullback-tensor-comparison).
Proof: use one flat K-flat representative pair and the actual quotient models
for O_L/varpi_L^m. Both paths send b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The equality respects every quotient map;
apply the actual coherent-system limit and its normalized substitutions. -/
def canonicalIntegralPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :=
    (sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
      E L ι X).map ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (integralTensorScalarComparison l E L ι X
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
      ((@constructibleIntegralTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom (integralPullbackScalarComparison l E L ι f M).hom
          (integralPullbackScalarComparison l E L ι f N).hom) =
    (integralPullbackScalarComparison l E L ι f
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
      ((@constructibleIntegralPullback l _ L _ _ _ X Y f hX hY)).map
        (integralTensorScalarComparison l E L ι Y M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj M)
        ((sfConstructibleIntegralScalarExtension 0 l
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι Y).obj N)).hom

/-- The rational scalar-extension square is the localized integral square.
Source: blueprint scalar-extension paragraph (blueprint:
def-pur-completed-pullback-tensor-comparison).
Proof: localize the preceding integral equality. Each operation comparison is
by definition the image of its integral component. Bilinearity then gives the
same square on every rational input, including identity scalar extensions. -/
def canonicalRationalPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) :=
    (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
        ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      (rationalTensorScalarComparison l E L ι X).hom.app
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M,((@rationalDerivedPullback l _ E
          _ _ _ X Y f hX hY)).obj N) ≫
      ((@rationalDerivedTensor l _ L _ _ _ X hX)).map
        (Prod.mkHom ((rationalPullbackScalarComparison l E L ι f).hom.app M)
          ((rationalPullbackScalarComparison l E L ι f).hom.app N)) =
    (rationalPullbackScalarComparison l E L ι f).hom.app
      (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) ≫
      ((@rationalDerivedPullback l _ L _ _ _ X Y f hX hY)).map
        ((rationalTensorScalarComparison l E L ι Y).hom.app (M,N)) ≫
      ((@canonicalRationalPullbackTensor l _ L _ _ _ X Y f hX hY)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)
        ((sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj N)).hom
end ScalarCompatibility



end WeilConjectures
