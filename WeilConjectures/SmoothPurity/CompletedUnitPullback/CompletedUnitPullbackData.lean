/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Supporting.ConstantCoefficientScalarNormalization
public import WeilConjectures.SmoothPurity.Completed.CompletedPrimitiveCounitComparison
public import WeilConjectures.AlgebraicGeometry.QuotientFrobenius.QuotientCornerFrobeniusStructures
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Completed coefficient units and coherent pullback

Source: blueprint, smooth purity, proof of
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, first sentence;
Bhatt--Scholze, Sections 3.5 and 6.5 and Lemma 6.8.2.
(blueprint: lem-pur-completed-unit-pullback-tower).

Every natural-number level n denotes positive exponent n+1. The regular module
on the coefficient sequence site has the actual quotient transitions. Its pullback
map is the adjoint of the actual coefficient ring map, so its finite components
are multiplication, rather than arbitrary identifications of objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf

namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The regular module on the existing quotient sequence ringed site.
Source: Bhatt--Scholze, Section 6.5; Stacks 0941
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def systemUnit (W : Scheme.{u}) : coefficientSequenceModules l E W :=
  SheafOfModules.unit
    ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf.{u, u} l E W))

/-- The whole strict quotient system in degree zero, localized before evaluation.
Source: Bhatt--Scholze, Section 6.5; Stacks 0941
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def systemObject (W : Scheme.{u}) : coefficientSequenceDerived l E W :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  (DerivedCategory.singleFunctor.{u + 2} _ 0).obj (systemUnit l E W)

/-- Whole-system coefficient multiplication, fixed by its actual adjoint ring map.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks 03D3, 0941
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def systemMultiplication {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (PrimitiveCounit.inverse.{u, u} l E f).obj (systemUnit l E Y) ⟶ systemUnit l E X :=
  ((Adjunction.ofIsRightAdjoint (PrimitiveCounit.direct.{u, u} l E f)).homEquiv
    (systemUnit l E Y) (systemUnit l E X)).symm
    (SheafOfModules.unitToPushforwardObjUnit.{u, u, u + 1, u + 1, u + 1}
      (F := PrimitiveCounit.base f)
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (K := coefficientSequenceTopology (ProEt.topology X))
      (S := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E Y))
      (R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E X))
      ⟨Functor.whiskerRight (PrimitiveCounit.ringMap.{u, u} l E f).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)

/-- The same multiplication as an arrow of whole derived systems.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks 0941
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def systemMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (PrimitiveCounit.pull l E f).obj (systemObject l E Y) ⟶ systemObject l E X :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E Y)
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E X)
  ((PrimitiveCounit.inverse.{u, u} l E f).mapDerivedCategorySingleFunctor.{u + 2, u + 2} 0).hom.app
      (systemUnit l E Y) ≫
    (DerivedCategory.singleFunctor.{u + 2} _ 0).map (systemMultiplication l E f)

/-- Actual finite coefficient-unit multiplication, the transpose of the ring map.
Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks 03D3
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def finiteMultiplication {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E f n).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) ⟶
        SheafOfModules.unit (integralCoefficientSheaf l E X n) :=
  ((Scheme.coefficientProEtaleModuleAdjunction.{u, u} f
    (CommRingCat.of (ULift.{u + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).homEquiv _ _).symm
    (SheafOfModules.unitToPushforwardObjUnit.{u, u, u + 1, u + 1, u + 1}
      (F := Scheme.proEtaleBaseChange f)
      (S := integralCoefficientSheaf l E Y n)
      (R := integralCoefficientSheaf l E X n)
      ⟨Functor.whiskerRight (Scheme.coefficientProEtaleDirectRingMap.{u, u} f
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).hom
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)

/-- Exact evaluation of the regular single system, using the standard localization.
Source: Stacks 0941
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def evaluationSingle (W : Scheme.{u}) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E W n).obj (systemObject l E W) ≅
      (DerivedCategory.singleFunctor.{u + 2} (normalizedDVRModules l E W n) 0).obj
        ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)) :=
  letI := HasDerivedCategory.standard (coefficientSequenceModules l E W)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E W n)
  ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor.{u + 2, u + 2} 0).app
    (systemUnit l E W)

/-- Uniform [0,0] bounds and a single constant stratum for the completed unit.
The object is the existing completed regular sheaf, never the discrete constant sheaf.
Source: Bhatt--Scholze, Sections 3.5 and 6.5, Definition 6.5.1
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def Admissible (W : Scheme.{u}) : Prop :=
  finiteTorConstructibleIntegral l E W (integralConstantCoefficientObject l E W) ∧
    ∀ n : ℕ, IsIso (constantCoefficientReductionMap l E W n) ∧
      proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension l E W n).obj
          (integralConstantCoefficientObject l E W)) ⊆ Set.Icc 0 0 ∧
      Scheme.HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E W n).obj
          (integralConstantCoefficientObject l E W)) 0 0 ∧
      IsLocallyConstantProEtaleModuleSheaf W (Padic.coefficientExtensionRing l E (n + 1))
        (SheafOfModules.unit (integralCoefficientSheaf l E W n))

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- Canonical whole-system identification and its augmentation. The finite maps are
fixed on every section; the augmentation is the actual adjunction unit followed by
that whole-system identification, and the finite reductions are the transposes of pi_n.
Source: Bhatt--Scholze, Sections 3.5 and 6.5; Stacks 0941
(blueprint: lem-pur-completed-unit-pullback-tower). -/
structure Reduction (W : Scheme.{u}) (S : CoefficientDerivedSystemCalculus l E W) where
  finite : ∀ n : ℕ, (coefficientSequenceEvaluation l E W n).obj (systemUnit l E W) ≅
    SheafOfModules.unit (integralCoefficientSheaf l E W n)
  finite_sections : ∀ (n : ℕ) (V : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj (systemUnit l E W)).val.obj V),
    HEq ((finite n).hom.val.app V x) x
  comparison : S.reduction.obj (integralConstantCoefficientObject l E W) ≅
    systemObject l E W
  reduction : ∀ n : ℕ,
    (coefficientSequenceDerivedEvaluation l E W n).map comparison.hom ≫
        (evaluationSingle l E W n).hom ≫
        (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).map
          (finite n).hom =
      (S.reductionEvaluation n).hom.app (integralConstantCoefficientObject l E W) ≫
        constantCoefficientReductionMap l E W n
  augmentation : integralConstantCoefficientObject l E W ≅
    (coefficientSequenceLimit l E W).obj (systemObject l E W)
  augmentation_eq : augmentation.hom =
    S.adjunction.unit.app (integralConstantCoefficientObject l E W) ≫
      (coefficientSequenceLimit l E W).map comparison.hom

/-- The published coefficient-system calculus, with its fixed reduction models.
Source: Stacks 0941 and the coefficient-system evaluation calculus
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def calculus (W : Scheme.{u}) : CoefficientDerivedSystemCalculus l E W :=
  (coefficientDerivedSystemEvaluationCalculus l E W).choose

/-- The actual completed unit as an object of the full constructible subcategory.
Only the membership proof is a parameter; its underlying object is fixed.
Source: Bhatt--Scholze, Section 6.5
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def integralObject (W : Scheme.{u})
    (h : sfIntegralConstructible l E W (integralConstantCoefficientObject l E W)) :
    sfIntegralConstructibleCategory l E W :=
  ⟨integralConstantCoefficientObject l E W, h⟩

/-- The coefficient unit in the recorded raw rationalization.
Source: blueprint purity conventions; Bhatt--Scholze, Section 6.5
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def rationalObject (W : Scheme.{u})
    (h : sfIntegralConstructible l E W (integralConstantCoefficientObject l E W)) :
    sfRationalConstructibleCategory l E W :=
  (sfRationalConstructibleLocalization l E W).obj (integralObject l E W h)

/-- The rational pullback's specified unchanged-object identification.
Source: the rational paragraph of def-weil-derived-pullback-tensor-hom
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def rationalSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hY : sfIntegralConstructible l E Y (integralConstantCoefficientObject l E Y)) :
    (rationalDerivedPullback l E f).obj (rationalObject l E Y hY) ≅
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj (integralObject l E Y hY)) :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1
    (rationalObject l E Y hY))

/-- The rational unit arrow is exactly the image of the integral arrow.
Source: blueprint purity conventions and rationalized pullback, arrow formula v tensor 1
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def rationalMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (hX : sfIntegralConstructible l E X (integralConstantCoefficientObject l E X))
    (hY : sfIntegralConstructible l E Y (integralConstantCoefficientObject l E Y))
    (v : (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ⟶
      integralConstantCoefficientObject l E X) :
    (rationalDerivedPullback l E f).obj (rationalObject l E Y hY) ⟶
      rationalObject l E X hX :=
  (rationalSource l E f hY).hom ≫
    (sfRationalConstructibleLocalization l E X).map (ObjectProperty.homMk v)

/-- The chosen subfield as an index of the already recorded common-stage category.
Source: blueprint purity conventions, E inside the fixed algebraic closure
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def coefficientStage (P : PurityFiniteSetting.{u}) :
    AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar :=
  ⟨P.extension, inferInstance⟩

/-- The existing small model of that very subfield, with its canonical algebra equivalence.
This is the coefficient model required by the recorded common-stage inclusion.
Source: def-weil-algebraically-closed-coefficients
(blueprint: lem-pur-completed-unit-pullback-tower). -/
abbrev coefficientModel (P : PurityFiniteSetting.{u}) :=
  AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar
    (coefficientStage P)

/-- The prime is a unit in every residue field over the fixed characteristic-p base.
The data comes from the already recorded local-ring unit and the residue homomorphism.
Source: purity conventions, ell distinct from p
(blueprint: lem-pur-completed-unit-pullback-tower). -/
instance residueInvertible (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    [W.Over (Spec (.of P.field.k))] (w : W) :
    Invertible (P.coefficients.l : W.residueField w) :=
  IsUnit.invertible (by
    simpa only [map_natCast] using
      (P.coefficientPrime_isUnit_stalk W (W ↘ Spec (.of P.field.k)) w).map (W.residue w).hom)

/-- The common-stage coefficient unit is literally the image at the chosen finite field.
Source: blueprint purity conventions, the pair (E,E_W)
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def commonObject (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    (h : sfIntegralConstructible P.coefficients.l (coefficientModel P) W
      (integralConstantCoefficientObject P.coefficients.l (coefficientModel P) W)) :
    generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar W :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := W) (coefficientStage P)).obj
      (rationalObject P.coefficients.l (coefficientModel P) W h)

/-- The specified unchanged-stage comparison for common-stage pullback.
Source: the common-stage paragraph of def-weil-derived-pullback-tensor-hom
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def commonSource (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (hY : sfIntegralConstructible P.coefficients.l (coefficientModel P) Y
      (integralConstantCoefficientObject P.coefficients.l (coefficientModel P) Y)) :
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar f).obj
        (commonObject P Y hY) ≅
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) (coefficientStage P)).obj
          ((rationalDerivedPullback P.coefficients.l (coefficientModel P) f).obj
            (rationalObject P.coefficients.l (coefficientModel P) Y hY)) :=
  eqToIso ((commonStageDerivedPullback_existsUnique P.coefficients.l P.coefficients.Qbar f)
    |>.exists.choose_spec.1 (commonObject P Y hY))

/-- The common-stage arrow is the actual inclusion of the rationalized integral arrow.
Source: blueprint purity conventions, represented over the same finite field E
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def commonMap (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    (hX : sfIntegralConstructible P.coefficients.l (coefficientModel P) X
      (integralConstantCoefficientObject P.coefficients.l (coefficientModel P) X))
    (hY : sfIntegralConstructible P.coefficients.l (coefficientModel P) Y
      (integralConstantCoefficientObject P.coefficients.l (coefficientModel P) Y))
    (v : (rationalDerivedPullback P.coefficients.l (coefficientModel P) f).obj
      (rationalObject P.coefficients.l (coefficientModel P) Y hY) ⟶
        rationalObject P.coefficients.l (coefficientModel P) X hX) :
    (commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar f).obj
      (commonObject P Y hY) ⟶ commonObject P X hX :=
  (commonSource P f hY).hom ≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) (coefficientStage P)).map v

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- All integral clauses, with actual maps and a whole-system reduction equation.
The comparison with the specified completed pullback is pinned by its K-flat Roos model.
Source: the node's six proof steps; Bhatt--Scholze, Sections 3.5 and 6.5
(blueprint: lem-pur-completed-unit-pullback-tower). -/
structure Core {X Y : Scheme.{u}} (f : X ⟶ Y) where
  admissibleX : Admissible l E X
  admissibleY : Admissible l E Y
  reductionX : Reduction l E X (calculus l E X)
  reductionY : Reduction l E Y (calculus l E Y)
  normalizedX : IsNormalizedCoefficientSequence l E X (systemObject l E X)
  normalizedY : IsNormalizedCoefficientSequence l E Y (systemObject l E Y)
  normalizedPull : IsNormalizedCoefficientSequence l E X
    ((PrimitiveCounit.pull l E f).obj (systemObject l E Y))
  finite_iso : ∀ n : ℕ, IsIso (finiteMultiplication l E f n)
  system_iso : IsIso (systemMap l E f)
  finite_components : ∀ n : ℕ,
    (coefficientSequenceEvaluation l E X n).map (systemMultiplication l E f) ≫
        (reductionX.finite n).hom =
      (PrimitiveCounit.inverseEvaluation l E f n).hom.app (systemUnit l E Y) ≫
        (integralOperationsLevelPullback l E f n).map (reductionY.finite n).hom ≫
          finiteMultiplication l E f n
  roos : PrimitiveCounit.RoosRealization l E X
  realization : integralDerivedPullback l E f ≅
    (calculus l E Y).reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X
  realization_model : PrimitiveCounit.PullModel l E f
    (calculus l E Y).toCoefficientDerivedSystemReduction roos realization
  unit : (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ≅
    integralConstantCoefficientObject l E X
  unit_formula : unit.hom =
    realization.hom.app (integralConstantCoefficientObject l E Y) ≫
      (coefficientSequenceLimit l E X).map
        ((PrimitiveCounit.pull l E f).map reductionY.comparison.hom ≫ systemMap l E f) ≫
      reductionX.augmentation.inv
  coherent_reduction :
    (calculus l E X).reduction.map unit.hom ≫ reductionX.comparison.hom =
      (calculus l E X).reduction.map
          (realization.hom.app (integralConstantCoefficientObject l E Y)) ≫
        (calculus l E X).adjunction.counit.app
          ((PrimitiveCounit.pull l E f).obj
            ((calculus l E Y).reduction.obj (integralConstantCoefficientObject l E Y))) ≫
        (PrimitiveCounit.pull l E f).map reductionY.comparison.hom ≫ systemMap l E f

/-- The actual algebra-equivalence transport from E to its recorded small model.
Source: the common-stage coefficient size convention
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def modelEmbedding (P : PurityFiniteSetting.{u}) :
    P.extension →ₐ[Padic P.coefficients.l] coefficientModel P :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm.toAlgHom

/-- The canonical scalar functor implementing that coefficient-size transport.
Source: def-weil-rationalization-karoubi and def-weil-algebraically-closed-coefficients
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def modelScalar (P : PurityFiniteSetting.{u}) (W : Scheme.{u}) :=
  sfRationalScalarExtension P.coefficients.l P.extension W 0
    (Nat.Prime.ne_zero (Fact.out : P.coefficients.l.Prime))
    (coefficientModel P) (modelEmbedding P)

/-- The normalized scalar-unit identification for the canonical small coefficient model.
Its inverse has actual quotient projections and zero shifted Roos coordinate.
Source: Bhatt--Scholze, Lemma 6.8.2, constant-coefficient scalar normalization
(blueprint: lem-pur-completed-unit-pullback-tower). -/
def modelUnit (P : PurityFiniteSetting.{u}) (W : Scheme.{u})
    (h : sfIntegralConstructible P.coefficients.l P.extension W
      (integralConstantCoefficientObject P.coefficients.l P.extension W))
    (h' : sfIntegralConstructible P.coefficients.l (coefficientModel P) W
      (integralConstantCoefficientObject P.coefficients.l (coefficientModel P) W)) :
    (modelScalar P W).obj (rationalObject P.coefficients.l P.extension W h) ≅
      rationalObject P.coefficients.l (coefficientModel P) W h' :=
  constantCoefficientRationalScalarIso P.coefficients.l P.extension (coefficientModel P)
    (modelEmbedding P) W P.field P.coefficients.different

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The same integral arrow presents both higher-coefficient unit identifications.
The integral and rational clauses use the literal field P.extension. The model clause
and its normalized square implement precisely the canonical common-stage size transport.
Source: blueprint purity conventions and the node's last paragraph
(blueprint: lem-pur-completed-unit-pullback-tower). -/
structure Result (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))] where
  core : Core P.coefficients.l P.extension f
  model : Core P.coefficients.l (coefficientModel P) f
  rational : IsIso (rationalMap P.coefficients.l P.extension f
    core.admissibleX.1.1 core.admissibleY.1.1 core.unit.hom)
  model_rational : IsIso (rationalMap P.coefficients.l (coefficientModel P) f
    model.admissibleX.1.1 model.admissibleY.1.1 model.unit.hom)
  model_square :
    (modelScalar P X).map (rationalMap P.coefficients.l P.extension f
        core.admissibleX.1.1 core.admissibleY.1.1 core.unit.hom) ≫
        (modelUnit P X core.admissibleX.1.1 model.admissibleX.1.1).hom =
      (rationalPullbackScalarComparison P.coefficients.l P.extension (coefficientModel P)
        (modelEmbedding P) f).hom.app
          (rationalObject P.coefficients.l P.extension Y core.admissibleY.1.1) ≫
        (rationalDerivedPullback P.coefficients.l (coefficientModel P) f).map
          (modelUnit P Y core.admissibleY.1.1 model.admissibleY.1.1).hom ≫
        rationalMap P.coefficients.l (coefficientModel P) f
          model.admissibleX.1.1 model.admissibleY.1.1 model.unit.hom
  common : IsIso (commonMap P f model.admissibleX.1.1 model.admissibleY.1.1
    (rationalMap P.coefficients.l (coefficientModel P) f
      model.admissibleX.1.1 model.admissibleY.1.1 model.unit.hom))

end WeilConjectures.CompletedUnitPullback
