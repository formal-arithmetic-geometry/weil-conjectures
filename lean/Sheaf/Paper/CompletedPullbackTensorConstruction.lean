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
import all Sheaf.Paper.FinitePullbackTensorUnitRepresentatives
import Sheaf.Paper.CompletedPullbackTensorAssociativityRepresentatives
import Sheaf.Paper.CompletedPullbackTensorUnitFromAssociativity
import Sheaf.Paper.CompletedPullbackTensorSignedRepresentatives
import all Sheaf.Paper.CompletedPullbackTensorEvaluationRepresentatives
import all Sheaf.Paper.CompletedPullbackTensorProofImplementations
import Sheaf.Paper.IntegralComparisonSequenceSystems
import Sheaf.Paper.FiniteQuotientPullbackDescent
import all Sheaf.Paper.StrictScalarPullbackComparison
import Sheaf.Paper.CompletedPullbackTensorTensorCounit
import Sheaf.Paper.FinitePullbackTensorQuotientRepresentatives
import all Sheaf.Paper.FinitePullbackTensorComparison
import Sheaf.Paper.CompletedPullbackTensorPullbackCounit
import all Sheaf.Paper.ProEtaleCanonicalTensorPullback
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients


public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Paper.CompletedPullbackTowerRealizations
/-! # Integral and rational pullback/tensor constructions

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: def-pur-completed-pullback-tensor-construction).

## Main definitions

* `canonicalIntegralPullbackTensor` is the prescribed comparison.
* The helper declarations fix its representative normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.all false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory


section CoherentSystems

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pullbackTensorSequenceRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = integralComparisonSequenceRingMap l E f := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply (pullbackTensorSequenceRing_existsUnique l E f).unique
    · exact (pullbackTensorSequenceRing_existsUnique l E f).exists.choose_spec
    · intro n U
      rfl

attribute [local irreducible] pullbackTensorIntegralTensorNormalization

/-- The systems used in the integral comparison are normalized, so the actual
reduction/limit counits on them are invertible.
Source: Stacks 0941; Bhatt--Scholze 3.4.12 (blueprint:
def-pur-completed-pullback-tensor-construction).
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
  have hY' : ∀ y : Y, IsUnit (l : Y.residueField y) :=
    fun y ↦ isUnit_of_invertible (l : Y.residueField y)
  have hX' : ∀ x : X, IsUnit (l : X.residueField x) :=
    fun x ↦ isUnit_of_invertible (l : X.residueField x)
  have h₁ := completedPullbackTensor_tensor_counit l E Y hY'
    (pullbackTensorCalculus l E Y) M.obj N.obj
  have heq : pullbackTensorSequenceInverse l E f =
      integralComparisonSequencePullback l E f := by
    unfold pullbackTensorSequenceInverse integralComparisonSequencePullback
    congr 1
    unfold pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
    rw [pullbackTensorSequenceRing_eq]
    rfl
  have h₂ := completedPullbackTensor_pullback_counit l E f hX' hY'
    (pullbackTensorCalculus l E X) (pullbackTensorCalculus l E Y)
    (pullbackTensorSequenceInverse l E f) heq M.obj
  have h₃ := completedPullbackTensor_pullback_counit l E f hX' hY'
    (pullbackTensorCalculus l E X) (pullbackTensorCalculus l E Y)
    (pullbackTensorSequenceInverse l E f) heq N.obj
  refine ⟨?_, ?_, ?_⟩
  · exact h₁
  · exact h₂
  · exact h₃

/-- The integral comparison in coherent coordinates is exactly Rlim of the
canonical system comparison, conjugated only by the specified coherent counits.
Source: Stacks 0941 and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorReferenceComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorReferencePullback l E f).obj
      ((pullbackTensorReferenceTensor l E Y).obj (M.obj,N.obj)) ≅
    (pullbackTensorReferenceTensor l E X).obj
      ((pullbackTensorReferencePullback l E f).obj M.obj,
        (pullbackTensorReferencePullback l E f).obj N.obj) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M N).1
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

attribute [local irreducible] pullbackTensorReferenceComparison

/-- The canonical completed integral comparison, transported from the actual
coherent-system Rlim map to the recorded completed operations and their full
constructible subcategories.
Source: Stacks 07A4 and 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
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
Source: Stacks 00YV, 03D2 (blueprint: def-pur-completed-pullback-tensor-construction).
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
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
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorLevelIntrinsic {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorLevelIntrinsic_existsUnique l E f n)

private theorem localizationIso_existsUnique
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (F G : C ⥤ E) (F' G' : D ⥤ E)
    (a : L ⋙ F' ≅ F) (b : L ⋙ G' ≅ G) (c : F ≅ G) :
    ∃! e : F' ≅ G', ∀ P : C,
      e.hom.app (L.obj P) ≫ b.hom.app P = a.hom.app P ≫ c.hom.app P := by
  letI : Localization.Lifting L W F F' := ⟨a⟩
  letI : Localization.Lifting L W G G' := ⟨b⟩
  let e := Localization.liftNatIso L W F G F' G' c
  have he (P : C) :
      e.hom.app (L.obj P) ≫ b.hom.app P = a.hom.app P ≫ c.hom.app P := by
    dsimp only [e, Localization.liftNatIso_hom]
    rw [Localization.liftNatTrans_app]
    change (a.hom.app P ≫ c.hom.app P ≫ b.inv.app P) ≫ b.hom.app P = _
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext L W
  intro P
  apply (cancel_mono (b.hom.app P)).1
  exact (he' P).trans (he P).symm

private theorem derivedCompositeIso_existsUnique
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    [HasDerivedCategory D₁] [HasDerivedCategory D₂]
    (A : C₁ ⥤ C₂) (B : C₂ ⥤ D₂) (C : C₁ ⥤ D₁) (D D₀ : D₁ ⥤ D₂)
    [A.Additive] [B.Additive] [C.Additive] [D.Additive] [D₀.Additive]
    [PreservesFiniteLimits A] [PreservesFiniteColimits A]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits C] [PreservesFiniteColimits C]
    [PreservesFiniteLimits D] [PreservesFiniteColimits D]
    (c₁ : A.mapHomologicalComplex (.up ℤ) ⋙ B.mapHomologicalComplex (.up ℤ) ≅
      C.mapHomologicalComplex (.up ℤ) ⋙ D₀.mapHomologicalComplex (.up ℤ)) (c₂ : D₀ ≅ D) :
    ∃! e : A.mapDerivedCategory ⋙ B.mapDerivedCategory ≅
      C.mapDerivedCategory ⋙ D.mapDerivedCategory,
      ∀ P : CochainComplex C₁ ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫
            D.mapDerivedCategory.map (C.mapDerivedCategoryFactors.hom.app P) ≫
            D.mapDerivedCategoryFactors.hom.app
              ((C.mapHomologicalComplex (.up ℤ)).obj P) =
          B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.hom.app P) ≫
            B.mapDerivedCategoryFactors.hom.app
              ((A.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map (c₁.hom.app P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c₂ (.up ℤ)).hom.app
              ((C.mapHomologicalComplex (.up ℤ)).obj P)) := by
  exact completedPullbackDerivedCompositeIso_existsUnique A B C D D₀ c₁ c₂

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived in
attribute [local irreducible] pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic in
/-- The full cochain normalization of finite evaluation, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorDerivedEvaluationNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f) : Prop :=
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
              (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P))

attribute [local irreducible] pullbackTensorDerivedEvaluationNormalization

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  pullbackTensorSequenceDerived in
attribute [local irreducible] pullbackTensorInverseEvaluationComplex pullbackTensorLevelIntrinsic in
/-- Evaluating the system inverse image gives the finite intrinsic inverse image;
the comparison is fixed on all cochain representatives by the two ordinary units.
Source: Stacks 0941, 03D2 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: apply the exact evaluation functor to a cochain representative. The
ordinary inverse-image/evaluation mate and the unit-normalized intrinsic
realization give the displayed chain comparison. Exact localization descends
it uniquely, since every derived object is represented by a complex. -/
theorem pullbackTensorDerivedEvaluation_existsUnique {X Y : Scheme.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    ∃! e : pullbackTensorSequenceDerived l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙ finiteDerivedPullback l E n f,
      pullbackTensorDerivedEvaluationNormalization l E f n e := by
  unfold pullbackTensorDerivedEvaluationNormalization
  let D : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
    sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f
  letI : D.Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI : PreservesFiniteLimits D :=
    sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI : PreservesFiniteColimits D :=
    sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  letI := integralOperationsLevelPullback_additive l E f n
  exact derivedCompositeIso_existsUnique (pullbackTensorSequenceInverse l E f)
    (coefficientSequenceEvaluation l E X n) (coefficientSequenceEvaluation l E Y n) D
    (integralOperationsLevelPullback l E f n)
    (pullbackTensorInverseEvaluationComplex l E f n).symm
    (pullbackTensorLevelIntrinsic l E f n)

/-- The actual evaluation comparison, including its fixed cochain normalization.
Source: Stacks 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorDerivedEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  pullbackTensorUniqueChoice (pullbackTensorDerivedEvaluation_existsUnique l E f n)

private theorem coherentTensor_representatives
    (W : Scheme.{u}) (M : coefficientSequenceDerived l E W) :
    ∃ P : CochainComplex (coefficientSequenceModules l E W) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        (J := coefficientSequenceTopology (ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let q := DerivedCategory.Q (C := coefficientSequenceModules l E W)
  let K := q.objPreimage M
  obtain ⟨P, a, hP, _, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  let : QuasiIso a := ha
  exact ⟨P, hP, ⟨asIso (q.map a) ≪≫ q.objObjPreimageIso M⟩⟩

private theorem tensorNatTrans_ext_resolving
    {B : Type*} [Category* B] {D : Type*} [Category* D]
    {E : Type*} [Category* E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ Y Z : B, P Y → P Z → a.app (q.obj Y, q.obj Z) =
      b.app (q.obj Y, q.obj Z)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨Y, hY, ⟨eY⟩⟩ := res X.1
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := res X.2
  let e := Iso.prod eY eZ
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h Y Z hY hZ]


section CoherentEvaluation
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] pullbackTensorSystemComparison pullbackTensorDerivedEvaluation
  pullbackTensorSequenceDerived pullbackTensorSequenceInverse
  finitePullbackTensorConstructionIso canonicalFinitePullbackTensor

/-- The coherent comparison whose limit defines μI evaluates to the same μF at
EVERY finite level, under the canonical tensor and inverse-image comparisons.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
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
  unfold canonicalFinitePullbackTensor
  exact completedPullbackTensor_evaluation_descent l E f n
    (pullbackTensorLevelIntrinsic l E f n)
    ((pullbackTensorLevelIntrinsic_existsUnique l E f n).exists.choose_spec)
    (pullbackTensorDerivedEvaluation l E f n) (by
      unfold pullbackTensorDerivedEvaluation pullbackTensorUniqueChoice
      simpa only [pullbackTensorDerivedEvaluationNormalization] using
        (pullbackTensorDerivedEvaluation_existsUnique l E f n).exists.choose_spec)
    (coherentTensor_representatives l E Y) M N

end CoherentEvaluation

section CoherentAssociativity
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorSequenceInverse

/-- Associativity for the actual coherent μ whose derived limit is the integral μ.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
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
  letI : MonoidalCategory (coefficientSequenceDerived l E Y) :=
    (pullbackTensorCalculus l E Y).systemClosed.monoidal
  letI : MonoidalCategory (coefficientSequenceDerived l E X) :=
    (pullbackTensorCalculus l E X).systemClosed.monoidal
  let F := pullbackTensorSequenceDerived l E f
  let μ := pullbackTensorSystemComparison l E f
  let a := assocLeftPath F μ
  let b := assocRightPath F μ
  have hab : a = b := tripleNatTrans_ext_resolving DerivedCategory.Q
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y))
    (coherentTensor_representatives l E Y) a b (by
      intro A B C hA hB hC
      exact completedPullbackTensor_associativity_representatives l E f A B C hA hB hC)
  exact NatTrans.congr_app hab (M,N,P)

end CoherentAssociativity

section CoherentBraiding
attribute [local irreducible] pullbackTensorCalculus pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorBraiding pullbackTensorSequenceInverse

attribute [local implicit_reducible] pullbackTensorSwap in
/-- Koszul braiding for the same coherent μ before taking its derived limit.
Source: Stacks 06YS, 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
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
  let F := pullbackTensorSequenceDerived l E f
  let TY := (pullbackTensorCalculus l E Y).systemClosed.tensor
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let μ := pullbackTensorSystemComparison l E f
  let σY := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y)
    (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E Y).systemTensorModel
  let σX := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    (pullbackTensorCalculus l E X).systemClosed
    (pullbackTensorCalculus l E X).systemTensorModel
  let a : TY ⋙ F ⟶ pullbackTensorSwap _ ⋙ (F.prod F) ⋙ TX :=
    Functor.whiskerRight σY.hom F ≫
      Functor.whiskerLeft (pullbackTensorSwap _) μ.hom
  let b : TY ⋙ F ⟶ pullbackTensorSwap _ ⋙ (F.prod F) ⋙ TX :=
    μ.hom ≫ Functor.whiskerLeft (F.prod F) σX.hom
  have hab : a = b := tensorNatTrans_ext_resolving DerivedCategory.Q
    (CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y))
    (coherentTensor_representatives l E Y) a b (by
      intro P Q hP hQ
      exact completedPullbackTensor_signed_representatives l E f P Q hP hQ)
  exact NatTrans.congr_app hab (M,N)

end CoherentBraiding

section CoherentUnit
universe a b c d
open MonoidalCategory

/-- Both unit equations for the coherent μ used to define the integral comparison.
Source: Stacks 03EL, 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: the associativity comparison and the coherent unit representative are
combined by the monoidal unit extraction lemma. -/
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
  exact completedPullbackTensor_unit_of_associativity l E f
    (pullbackTensorSystemComparison_associativity l E f)

end CoherentUnit

end CoherentSystems

section QuotientCompatibility
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Cache additive finite inverse image with the explicitly sized coefficient ring.
Source: Stacks 03D2 (blueprint: def-pur-completed-pullback-tensor-construction). -/
instance pullbackTensorFiniteAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
  sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f

/-- Cache the actual quotient extension's published additive structure.
Source: Stacks 06YY (blueprint: def-pur-completed-pullback-tensor-construction). -/
instance pullbackTensorQuotientAdditive (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientExtension l E W h).Additive :=
  coefficientFiniteQuotientExtensionAdditive l E W h

/-- The quotient/pullback comparison preserves the two actual adjunction units.
Source: Stacks 06YY and 03D2 (blueprint: def-pur-completed-pullback-tensor-construction).
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
  exact completedPullbackTensorQuotientOrdinary l E f h

/-- The unit-normalized ordinary quotient/pullback comparison.
Source: Stacks 06YY and 03D2 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotientOrdinary {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :=
  pullbackTensorUniqueChoice (pullbackTensorQuotientOrdinary_existsUnique l E f h)

attribute [local irreducible] pullbackTensorQuotientOrdinary

/-- Finite constant-coefficient inverse image preserves K-flat complexes.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
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
  exact completedPullbackTensorFiniteGood l E f n P hP

/-- The ordinary quotient/pullback comparison on complexes, with both composition
identifications and all additive instances supplied explicitly.
Source: Stacks 06YY, 07A4 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotientComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    (sfIntrinsicPullback
      (finiteCoefficientRing l E (m + 1)) f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientFiniteQuotientExtension l E X h).mapHomologicalComplex (.up ℤ) ≅
    (coefficientFiniteQuotientExtension l E Y h).mapHomologicalComplex (.up ℤ) ⋙
      (sfIntrinsicPullback
        (finiteCoefficientRing l E (n + 1)) f).mapHomologicalComplex (.up ℤ) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
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

attribute [local irreducible] pullbackTensorQuotientComplex

/-- The full K-flat normalization of quotient pullback, kept behind a named predicate so
selecting its unique isomorphism does not repeatedly type-check the full square.
Source: Stacks 07A4, 0941 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotientNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m)
    (e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f) : Prop :=
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
          DerivedCategory.Q.map ((pullbackTensorQuotientComplex l E f h).hom.app P)

attribute [local irreducible] pullbackTensorQuotientNormalization

section QuotientDescent
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] coefficientFiniteQuotientExtension coefficientFiniteQuotientDerived

/-- The quotient/pullback isomorphism is fixed by its full K-flat counit square.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: the preceding ordinary comparison on K-flat representatives identifies
the two derived functors. The universal quotient counit and exact-pullback
factorization give precisely this square. K-flat localization determines a
unique natural isomorphism from the displayed squares. -/
theorem pullbackTensorQuotient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! e : finiteDerivedPullback l E m f ⋙ coefficientFiniteQuotientDerived l E X h ≅
      coefficientFiniteQuotientDerived l E Y h ⋙ finiteDerivedPullback l E n f,
      pullbackTensorQuotientNormalization l E f h e := by
  unfold pullbackTensorQuotientNormalization
  exact finiteQuotientPullbackDescent l E f h
    (pullbackTensorQuotientComplex l E f h) (pullbackTensorFiniteGood l E f m)

end QuotientDescent


/-- The derived quotient/pullback comparison with its fixed K-flat normalization.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction). -/
def pullbackTensorQuotient {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  pullbackTensorUniqueChoice (pullbackTensorQuotient_existsUnique l E f h)

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
attribute [local irreducible] finitePullbackTensorConstructionIso
  finitePullbackTensorConstruction coefficientFiniteQuotientDerived
  coefficientFiniteQuotientModel pullbackTensorQuotient

private theorem pullbackTensorQuotientComplex_f {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E Y m) ℤ) (i : ℤ) :
    ((pullbackTensorQuotientComplex l E f h).hom.app P).f i =
      (pullbackTensorQuotientOrdinary l E f h).hom.app (P.X i) := by
  unfold pullbackTensorQuotientComplex
  simp

-- Give the quotient tensorator its intrinsic source and target once. This avoids
-- reducing the entire chosen evaluation calculus at every whiskering below.
private def quotientTensorForDescent (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    finiteIntrinsicDerivedTensor l E W m ⋙ coefficientFiniteQuotientDerived l E W h ≅
      (coefficientFiniteQuotientDerived l E W h).prod
        (coefficientFiniteQuotientDerived l E W h) ⋙ finiteIntrinsicDerivedTensor l E W n :=
  (pullbackTensorCalculus l E W).quotientCalculus.tensor h

attribute [local irreducible] quotientTensorForDescent

private theorem quotientTensorForDescent_app (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (M N : proEtaleDerivedCategory W (finiteCoefficientRing l E (m + 1))) :
    (quotientTensorForDescent l E W h).hom.app (M, N) =
      ((pullbackTensorCalculus l E W).quotientCalculus.tensor h).hom.app (M, N) := by
  unfold quotientTensorForDescent
  rfl

-- This descent only uses naturality and resolving isomorphisms. Keeping it
-- abstract avoids normalizing concrete derived-category functors in its proof.
private theorem quotientTensor_square_of_resolutions
    {A B C D K : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* K]
    (q : K ⥤ A) (P : ObjectProperty K)
    (res : ∀ M : A, ∃ U : K, P U ∧ Nonempty (q.obj U ≅ M))
    (Fm : A ⥤ B) (Fn : C ⥤ D) (QX : B ⥤ D) (QY : A ⥤ C)
    (Tm : A × A ⥤ A) (TX : B × B ⥤ B) (TY : C × C ⥤ C) (Tn : D × D ⥤ D)
    (μm : Tm ⋙ Fm ≅ Fm.prod Fm ⋙ TX) (μn : TY ⋙ Fn ≅ Fn.prod Fn ⋙ Tn)
    (τX : TX ⋙ QX ≅ QX.prod QX ⋙ Tn) (τY : Tm ⋙ QY ≅ QY.prod QY ⋙ TY)
    (e : Fm ⋙ QX ≅ QY ⋙ Fn)
    (h : ∀ U V : K, P U → P V →
      QX.map (μm.hom.app (q.obj U, q.obj V)) ≫
        τX.hom.app (Fm.obj (q.obj U), Fm.obj (q.obj V)) ≫
        Tn.map (Prod.mkHom (e.hom.app (q.obj U)) (e.hom.app (q.obj V))) =
      e.hom.app (Tm.obj (q.obj U, q.obj V)) ≫
        Fn.map (τY.hom.app (q.obj U, q.obj V)) ≫
        μn.hom.app (QY.obj (q.obj U), QY.obj (q.obj V)))
    (M N : A) :
    QX.map (μm.hom.app (M, N)) ≫ τX.hom.app (Fm.obj M, Fm.obj N) ≫
        Tn.map (Prod.mkHom (e.hom.app M) (e.hom.app N)) =
      e.hom.app (Tm.obj (M, N)) ≫ Fn.map (τY.hom.app (M, N)) ≫
        μn.hom.app (QY.obj M, QY.obj N) := by
  let a : Tm ⋙ Fm ⋙ QX ⟶ (QY ⋙ Fn).prod (QY ⋙ Fn) ⋙ Tn :=
    Functor.whiskerRight μm.hom QX ≫
      Functor.whiskerLeft (Fm.prod Fm) τX.hom ≫
      Functor.whiskerRight (NatTrans.prod e.hom e.hom) Tn
  let b : Tm ⋙ Fm ⋙ QX ⟶ (QY ⋙ Fn).prod (QY ⋙ Fn) ⋙ Tn :=
    Functor.whiskerLeft Tm e.hom ≫ Functor.whiskerRight τY.hom Fn ≫
      Functor.whiskerLeft (QY.prod QY) μn.hom
  have hab : a = b := tensorNatTrans_ext_resolving q P res a b (by
    intro U V hU hV
    exact h U V hU hV)
  exact NatTrans.congr_app hab (M, N)

/-- The finite comparison commutes with every derived quotient B_m to B_n,
including m = n. All four change-of-coefficient arrows are the normalized ones.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
Proof: on flat-term K-flat representatives, the representative lemma computes both
paths by the formula 1 tensor f*(x tensor y) mapping to f*(1 tensor x) tensor
f*(1 tensor y). The ordinary unit, cochain degree, and derived counit equations
supply its normalization hypotheses. The two paths are natural transformations.
Every derived object is isomorphic to a localized flat-term K-flat complex;
naturality along these resolving isomorphisms extends the square to all inputs. -/
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
  have hsq := quotientTensor_square_of_resolutions
    (A := proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1)))
    (B := proEtaleDerivedCategory X (finiteCoefficientRing l E (m + 1)))
    (C := proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)))
    (D := proEtaleDerivedCategory X (finiteCoefficientRing l E (n + 1)))
    (DerivedCategory.Q (C := normalizedDVRModules l E Y m))
    (proEtaleFlatRepresentatives Y (integralCoefficientCommRingSheaf l E Y m))
    (finiteTensor_flat_representatives l E Y m)
    (finiteDerivedPullback l E m f) (finiteDerivedPullback l E n f)
    (coefficientFiniteQuotientDerived l E X h) (coefficientFiniteQuotientDerived l E Y h)
    (finiteIntrinsicDerivedTensor l E Y m) (finiteIntrinsicDerivedTensor l E X m)
    (finiteIntrinsicDerivedTensor l E Y n) (finiteIntrinsicDerivedTensor l E X n)
    (finitePullbackTensorConstructionIso l E f m) (finitePullbackTensorConstructionIso l E f n)
    (quotientTensorForDescent l E X h) (quotientTensorForDescent l E Y h)
    (pullbackTensorQuotient l E f h) (by
      intro P Q hP hQ
      have hr := finitePullbackTensor_quotient_representatives l E f h
        (pullbackTensorQuotientOrdinary l E f h)
        (by
          unfold pullbackTensorQuotientOrdinary pullbackTensorUniqueChoice
          exact (pullbackTensorQuotientOrdinary_existsUnique l E f h).exists.choose_spec)
        (pullbackTensorQuotientComplex l E f h)
        (pullbackTensorQuotientComplex_f l E f h)
        (pullbackTensorFiniteGood l E f m) (pullbackTensorQuotient l E f h)
        (by
          unfold pullbackTensorQuotient pullbackTensorUniqueChoice
          simpa only [pullbackTensorQuotientNormalization] using
            (pullbackTensorQuotient_existsUnique l E f h).exists.choose_spec) P Q hP hQ
      dsimp only [Functor.comp_obj] at hr ⊢
      simp only [finiteEvaluationComparison_app, quotientTensorForDescent_app] at hr ⊢
      exact hr) M N
  unfold canonicalFinitePullbackTensor
  dsimp only [Functor.comp_obj] at hsq ⊢
  simp only [finiteEvaluationComparison_app, quotientTensorForDescent_app] at hsq ⊢
  exact hsq
/-- The finite comparison commutes with every derived quotient B_m to B_n,
including m = n. All four change-of-coefficient arrows are the normalized ones.
Source: Stacks 06YY and 07A4 (blueprint: def-pur-completed-pullback-tensor-construction).
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
def-pur-completed-pullback-tensor-construction).
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
def-pur-completed-pullback-tensor-construction). -/
def canonicalRationalPullbackTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@RationalPullbackTensorComparison l _ E _ _ _ X Y f hX hY) := fun M N ↦
  pullbackTensorUniqueChoice
    ((@canonicalRationalPullbackTensor_existsUnique l _ E _ _ _ X Y f hX hY) M N)
end LocalizationComparison

section CommonComparison
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open GeneralAlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The rational comparison in any common finite stage, with all four prescribed
pullback/tensor transition comparisons included.
Source: blueprint common-stage paragraph
(blueprint: def-pur-completed-pullback-tensor-construction).
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

end CommonComparison



section ScalarCompatibility
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- Integral scalar extension commutes with the comparison arrow, including
ramified extensions, under the recorded canonical operation comparisons.
Source: blueprint scalar-extension paragraph; Stacks 0941 and 07A4
(blueprint: def-pur-completed-pullback-tensor-construction).
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

section RationalScalarProof

private theorem comparisonMapHEq {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y X' Y' : C}
    {a : X ⟶ Y} {b : X' ⟶ Y'} (h : HEq a b) (hx : X = X') (hy : Y = Y') :
    HEq (F.map a) (F.map b) := by
  cases hx; cases hy; cases h
  rfl

private theorem comparisonApplyHEq {A : Sort*} {B : A → Sort*}
    {a b : A} (h : a = b) (g : ∀ a, B a) : HEq (g a) (g b) := by
  cases h
  rfl

private theorem comparisonProdHEq {C : Type*} [Category* C]
    {A B A' B' D E D' E' : C}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : D ⟶ E} {b' : D' ⟶ E'}
    (h : HEq a a') (h' : HEq b b')
    (ha : A = A') (hb : B = B') (hd : D = D') (he : E = E') :
    HEq (Prod.mkHom a b) (Prod.mkHom a' b') := by
  cases ha; cases hb; cases hd; cases he
  cases h; cases h'
  rfl

private theorem comparisonLocalizationMapHEq
    {R : Type*} [CommRing R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (p : R) {A B : C} (a : A ⟶ B) :
    HEq ((ScalarLocalization.localization R C p).map a)
      ((1 : Localization.Away p) ⊗ₜ[R] a) := by
  rfl

attribute [local irreducible] canonicalIntegralPullbackTensor
attribute [local irreducible] integralPullbackScalarComparison integralTensorScalarComparison
  constructibleIntegralPullback constructibleIntegralTensor sfConstructibleIntegralScalarExtension

/-- The rational scalar-extension square is the localized integral square.
Source: blueprint scalar-extension paragraph (blueprint:
def-pur-completed-pullback-tensor-construction).
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
  let Q (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u}) :=
    sfRationalConstructibleLocalization l K W
  let S (W : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
  let s (W : Scheme.{u}) := sfRationalScalarExtension l E W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let F (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] := constructibleIntegralPullback l K f
  let r (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] := rationalDerivedPullback l K f
  let T (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u})
      [∀ w : W, Invertible (l : W.residueField w)] := constructibleIntegralTensor l K W
  let t (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u})
      [∀ w : W, Invertible (l : W.residueField w)] := rationalDerivedTensor l K W
  have hs (W : Scheme.{u}) (A : sfRationalConstructibleCategory l E W) :
      (s W).obj A = (Q L W).obj ((S W).obj A.obj) :=
    sfRationalScalarExtension_obj l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A
  have hr (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (A : sfRationalConstructibleCategory l K Y) :
      (r K).obj A = (Q K X).obj ((F K).obj A.obj) :=
    by simpa only [r, F, Q, rationalDerivedPullback,
      sfRationalConstructibleLocalization, ScalarLocalization.localization] using
      (rationalDerivedPullback_existsUnique l K f).exists.choose_spec.2.1 A
  have ht (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (W : Scheme.{u})
      [∀ w : W, Invertible (l : W.residueField w)]
      (AB : sfRationalConstructibleCategory l K W × sfRationalConstructibleCategory l K W) :
      (t K W).obj AB = (Q K W).obj ((T K W).obj (AB.1.obj, AB.2.obj)) :=
    by simpa only [t, T, Q, rationalDerivedTensor,
      sfRationalConstructibleLocalization, ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l K W).exists.choose_spec.1 AB
  have ms (W : Scheme.{u}) {A B : sfIntegralConstructibleCategory l E W} (a : A ⟶ B) :
      HEq ((s W).map ((Q E W).map a)) ((Q L W).map ((S W).map a)) := by
    have h := sfRationalScalarExtension_map_tmul l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι A B a 1
    simp only [map_one] at h
    have hm := comparisonLocalizationMapHEq
      (Padic.coefficientExtensionUniformizer l L) ((S W).map a)
    convert h.trans hm.symm using 0
    rfl
  have mr {A B : sfIntegralConstructibleCategory l L Y} (a : A ⟶ B) :
      HEq ((r L).map ((Q L Y).map a)) ((Q L X).map ((F L).map a)) := by
    have h := (rationalDerivedPullback_existsUnique l L f).exists.choose_spec.2.2 A B a 1
    have hm := comparisonLocalizationMapHEq
      (Padic.coefficientExtensionUniformizer l L) ((F L).map a)
    convert h.trans hm.symm using 0
    rfl
  have mt {A A' B B' : sfIntegralConstructibleCategory l L X}
      (a : A ⟶ A') (b : B ⟶ B') :
      HEq ((t L X).map (Prod.mkHom ((Q L X).map a) ((Q L X).map b)))
        ((Q L X).map ((T L X).map (Prod.mkHom a b))) := by
    obtain ⟨β, hβ, hp⟩ := (rationalDerivedTensor_existsUnique l L X).exists.choose_spec.2
      ((Q L X).obj A) ((Q L X).obj A') ((Q L X).obj B) ((Q L X).obj B')
    dsimp only [t, rationalDerivedTensor]
    rw [hβ]
    have h := hp a b 1 1
    simp only [one_mul] at h
    have hm := comparisonLocalizationMapHEq
      (Padic.coefficientExtensionUniformizer l L) ((T L X).map (Prod.mkHom a b))
    convert h.trans hm.symm using 0
    rfl
  have hmu (K : Type u) [Field K] [Algebra (Padic l) K]
      [FiniteDimensional (Padic l) K] (A B : sfRationalConstructibleCategory l K Y) :
      HEq (canonicalRationalPullbackTensor l K f A B).hom
        ((Q K X).map (canonicalIntegralPullbackTensor l K f A.obj B.obj).hom) :=
    by simpa only [canonicalRationalPullbackTensor, pullbackTensorUniqueChoice, Q] using
      (canonicalRationalPullbackTensor_existsUnique l K f A B).exists.choose_spec
  have hp (A : sfRationalConstructibleCategory l E Y) :
      HEq ((rationalPullbackScalarComparison l E L ι f).hom.app A)
        ((Q L X).map (integralPullbackScalarComparison l E L ι f A.obj).hom) :=
    by simpa only [rationalPullbackScalarComparison, Q] using
      (rationalPullbackScalarComparison_existsUnique l E L ι f).exists.choose_spec A
  have hq (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
      (A B : sfRationalConstructibleCategory l E W) :
      HEq ((rationalTensorScalarComparison l E L ι W).hom.app (A,B))
        ((Q L W).map (integralTensorScalarComparison l E L ι W A.obj B.obj).hom) :=
    by simpa only [rationalTensorScalarComparison, Q] using
      (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec A B
  -- The six vertices have the prescribed integral object formulas.
  have hsrc : (s X).obj ((r E).obj ((t E Y).obj (M,N))) =
      (Q L X).obj ((S X).obj ((F E).obj ((T E Y).obj (M.obj,N.obj)))) := by
    rw [hs, hr, ht]
    rfl
  have hmid : (s X).obj ((t E X).obj ((r E).obj M,(r E).obj N)) =
      (Q L X).obj ((S X).obj ((T E X).obj ((F E).obj M.obj,(F E).obj N.obj))) := by
    rw [hs, ht, hr, hr]
    rfl
  have hmid' : (t L X).obj ((s X).obj ((r E).obj M),(s X).obj ((r E).obj N)) =
      (Q L X).obj ((T L X).obj ((S X).obj ((F E).obj M.obj),
        (S X).obj ((F E).obj N.obj))) := by
    rw [ht, hs, hs, hr, hr]
    rfl
  have htgt : (t L X).obj ((r L).obj ((s Y).obj M),(r L).obj ((s Y).obj N)) =
      (Q L X).obj ((T L X).obj ((F L).obj ((S Y).obj M.obj),
        (F L).obj ((S Y).obj N.obj))) := by
    rw [ht, hr, hr, hs, hs]
    rfl
  have hmidR : (r L).obj ((s Y).obj ((t E Y).obj (M,N))) =
      (Q L X).obj ((F L).obj ((S Y).obj ((T E Y).obj (M.obj,N.obj)))) := by
    rw [hr, hs, ht]
    rfl
  have hmidR' : (r L).obj ((t L Y).obj ((s Y).obj M,(s Y).obj N)) =
      (Q L X).obj ((F L).obj ((T L Y).obj ((S Y).obj M.obj,(S Y).obj N.obj))) := by
    rw [hr, ht, hs, hs]
    rfl
  -- Identify all six arrows with their integral localizations.
  have h1 := (comparisonMapHEq (s X) (hmu E M N)
    (by rw [hr, ht]; rfl) (by rw [ht, hr, hr]; rfl)).trans
      (ms X (canonicalIntegralPullbackTensor l E f M.obj N.obj).hom)
  have h2 := (hq X ((r E).obj M) ((r E).obj N)).trans
    (comparisonApplyHEq (congrArg₂ Prod.mk (hr E M) (hr E N))
      (fun AB : sfRationalConstructibleCategory l E X ×
          sfRationalConstructibleCategory l E X ↦
        (Q L X).map (integralTensorScalarComparison l E L ι X AB.1.obj AB.2.obj).hom))
  have h3 := (comparisonMapHEq (t L X)
    (comparisonProdHEq (hp M) (hp N)
      (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl))
    (congrArg₂ Prod.mk (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hs, hr]; rfl))
    (congrArg₂ Prod.mk (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl)
      (by dsimp only [Functor.comp_obj]; rw [hr, hs]; rfl))).trans
        (mt (integralPullbackScalarComparison l E L ι f M.obj).hom
          (integralPullbackScalarComparison l E L ι f N.obj).hom)
  have h4 := (hp ((t E Y).obj (M,N))).trans
    (comparisonApplyHEq (ht E Y (M,N))
      (fun A : sfRationalConstructibleCategory l E Y ↦
        (Q L X).map (integralPullbackScalarComparison l E L ι f A.obj).hom))
  have h5 := (comparisonMapHEq (r L) (hq Y M N) (by dsimp only [Functor.comp_obj]; rw [hs, ht]; rfl)
    (by dsimp only [Functor.comp_obj, Functor.prod_obj]; rw [ht, hs, hs]; rfl)).trans
      (mr (integralTensorScalarComparison l E L ι Y M.obj N.obj).hom)
  have h6 := (hmu L ((s Y).obj M) ((s Y).obj N)).trans
    (comparisonApplyHEq (congrArg₂ Prod.mk (hs Y M) (hs Y N))
      (fun AB : sfRationalConstructibleCategory l L Y ×
          sfRationalConstructibleCategory l L Y ↦
        (Q L X).map (canonicalIntegralPullbackTensor l L f AB.1.obj AB.2.obj).hom))
  -- Functoriality transports the integral square to the rational square.
  apply eq_of_heq
  exact (heq_comp hsrc hmid htgt h1 (heq_comp hmid hmid' htgt h2 h3)).trans
    ((heq_of_eq (by
      have h := congrArg (Q L X).map
        (canonicalIntegralPullbackTensor_scalar l E L ι f M.obj N.obj)
      simp only [Functor.map_comp] at h
      convert h using 0
      rfl)).trans
      (heq_comp hsrc hmidR htgt h4 (heq_comp hmidR hmidR' htgt h5 h6)).symm)

end RationalScalarProof

/-- Integral scalar extension commutes with the comparison arrow, including
ramified extensions, under the recorded canonical operation comparisons.
Source: blueprint scalar-extension paragraph; Stacks 0941 and 07A4
(blueprint: def-pur-completed-pullback-tensor-construction).
Proof: use one flat K-flat representative pair and the actual quotient models
for O_L/varpi_L^m. Both paths send b tensor (x tensor y) to
(b tensor x) tensor (1 tensor y). The equality respects every quotient map;
apply the actual coherent-system limit and its normalized substitutions. -/
def canonicalIntegralPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  type_of% (canonicalIntegralPullbackTensor_scalar l E L ι f M N)

/-- The rational scalar-extension square is the localized integral square.
Source: blueprint scalar-extension paragraph (blueprint:
def-pur-completed-pullback-tensor-construction).
Proof: localize the preceding integral equality. Each operation comparison is
by definition the image of its integral component. Bilinearity then gives the
same square on every rational input, including identity scalar extensions. -/
def canonicalRationalPullbackTensor_scalar_condition {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop :=
  type_of% (canonicalRationalPullbackTensor_scalar l E L ι f M N)

end ScalarCompatibility




end WeilConjectures
