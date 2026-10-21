/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact

/-! # Quotient-limit realization and primitive coherent-counit comparisons

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
with the strict Roos normalization and the coherent coefficient-system adjunction
(blueprint: lem-pur-completed-primitive-counit-comparison).

Natural number n means positive coefficient exponent n+1. All systems are derived
before evaluation, and the site has independent object and morphism universes t+1 and t.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall


universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
namespace WeilConjectures
attribute [local irreducible] integralCompletedTensor integralCompletedTensorComparison
  integralDerivedPullback integralDerivedPullbackComparison
namespace PrimitiveCounit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual base-change functor of the vertical sequence sites.
Source: Stacks 0941 and 09A5
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def base {X Y : Scheme.{t}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Vertical sequence base change is continuous.
Source: Stacks 0941 and 09A5
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: restrict a vertical covering sieve to its fixed coefficient level. Its image
is a pro-etale covering by continuity of pro-etale base change. Horizontal arrows
keep the same level, so the slice sheaf conditions assemble on the sequence site. -/
theorem base_continuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (base f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  sorry

attribute [instance] base_continuous

/-- The sequence ring's section at (n,U) is the actual finite constant-ring section.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: unfold the sequence presheaf, uncurry and ofOpSequence at the object (n,U).
The object is the finite constant sheaf evaluated at U; no transition is involved. -/
theorem section_eq (W : Scheme.{t}) (U : (ℕ × W.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingSheaf l E W).obj.obj U =
      ((constantSheaf (Scheme.ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (U.unop.1 + 1))))).obj.obj (op U.unop.2) := by
  sorry

/-- The constant-section component, transported through the explicit section identity.
Source: Stacks 0H7J, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def ringComponent {X Y : Scheme.{t}} (f : X ⟶ Y) (U : (ℕ × Y.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingSheaf l E Y).obj.obj U ⟶
      (coefficientSequenceCommRingSheaf l E X).obj.obj ((base f).op.obj U) :=
  eqToHom (section_eq l E Y U) ≫
    (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (U.unop.1 + 1))))).hom.app (op U.unop.2) ≫
    eqToHom (section_eq l E X ((base f).op.obj U)).symm

/-- Constant-section components respect vertical and quotient arrows simultaneously.
Source: Stacks 0H7J, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: vertical naturality is that of the constant-section map; horizontal naturality
is its naturality in the coefficient ring, checked under sheafification adjunction.
Both transposes send a coefficient to the same constant section after quotient. -/
theorem ringMap_natural {X Y : Scheme.{t}} (f : X ⟶ Y)
    {U V : (ℕ × Y.ProEt)ᵒᵖ} (a : U ⟶ V) :
    (coefficientSequenceCommRingSheaf l E Y).obj.map a ≫ ringComponent l E f V =
      ringComponent l E f U ≫
        (coefficientSequenceCommRingSheaf l E X).obj.map ((base f).op.map a) := by
  sorry

/-- The sequence ring map assembled from the actual constant-section components.
Source: Stacks 0H7J, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def ringMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSheaf l E Y ⟶
      ((base f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X) :=
  ⟨{ app := ringComponent l E f
     naturality := fun {_ _} a ↦ ringMap_natural l E f a }⟩

/-- Canonical sectionwise system direct image with restricted coefficient action.
Source: Stacks 03D7, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def direct {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y :=
  SheafOfModules.pushforward (F := base f)
    ⟨Functor.whiskerRight (ringMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The system inverse image is the left adjoint to this specified direct image.
Source: Stacks 03D3 and 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: transport the vertical sequence sites to coefficient-sized skeletons.
Module left Kan extension followed by module sheafification gives a left adjoint
to the displayed pushforward. Transport back along the site equivalences. This
retains all quotient arrows and the prescribed scalar action. -/
theorem direct_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (direct l E f).IsRightAdjoint := by
  sorry

attribute [instance] direct_isRightAdjoint

/-- Geometric inverse image on whole strict systems, defined by its universal property.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def inverse {X Y : Scheme.{t}} (f : X ⟶ Y) := (direct l E f).leftAdjoint

/-- Constant-coefficient geometric inverse image is exact on whole systems.
Source: Stacks 03D2, 0941; lem-coef-semilinear-derived-sections
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: evaluation of the adjunction identifies its left adjoint with the canonical
finite-level module inverse image. Those functors are exact for constant coefficients.
Kernels and cokernels of systems are computed at every level. Their comparisons
are therefore isomorphisms. The additive right adjoint makes the left adjoint additive. -/
theorem inverse_exact {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (inverse l E f).Additive ∧ PreservesFiniteLimits (inverse l E f) ∧
      PreservesFiniteColimits (inverse l E f) := by
  sorry

/-- Additivity of geometric system inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance inverseAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (inverse l E f).Additive := (inverse_exact l E f).1

/-- Left exactness of geometric system inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance inverseLimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteLimits (inverse l E f) := (inverse_exact l E f).2.1

/-- Right exactness of geometric system inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance inverseColimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteColimits (inverse l E f) := (inverse_exact l E f).2.2

/-- The exact geometric inverse image on ordinary unbounded derived whole systems.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def pull {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (inverse l E f).mapDerivedCategory

/-- Additivity of finite geometric inverse image from its existing adjunction theorem.
Source: Stacks 03D2 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance levelAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E f n).Additive :=
  integralOperationsLevelPullback_additive l E f n

/-- Exactness at each finite constant coefficient, for the derived evaluation formula.
Source: Stacks 03D2 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance levelLimits {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
  (Scheme.coefficientProEtaleModulePullback_exact.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).1

/-- Right exactness at each finite constant coefficient.
Source: Stacks 03D2 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
instance levelColimits {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
  (Scheme.coefficientProEtaleModulePullback_exact.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))).2

/-- Sectionwise direct image commutes with finite evaluation, including its scalar action.
Source: Stacks 03D7, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: both functors evaluate sections at (n,baseChange U), with the same module map.
The structural ring homomorphism is ringComponent, whose transports are the explicit
sequence-section identities. Unfold them; equality of ring actions and morphisms
then gives equality of module sheaves and of functors. -/
theorem directEvaluation_eq {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    direct l E f ⋙ coefficientSequenceEvaluation l E Y n =
      coefficientSequenceEvaluation l E X n ⋙
        Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) := by
  sorry

/-- The ordinary inverse-image evaluation is uniquely normalized by the actual units.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison).
Proof: use the levelwise module adjunction on a sectionwise free presentation.
The system adjunction at level n has exactly this evaluated unit. On free generators
send the universal inverse-image generator to the finite inverse-image generator.
The relations, sheafification and horizontal quotient maps commute with this map.
The reverse construction gives an inverse; the generators prove uniqueness and naturality. -/
theorem inverseEvaluation_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    ∃! ξ : inverse l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n,
      ∀ M : coefficientSequenceModules l E Y,
        (coefficientSequenceEvaluation l E Y n).map
            ((Adjunction.ofIsRightAdjoint (direct l E f)).unit.app M) ≫
          (eqToIso (directEvaluation_eq l E f n)).hom.app ((inverse l E f).obj M) ≫
          (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1))))).map (ξ.hom.app M) =
        (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
              ((coefficientSequenceEvaluation l E Y n).obj M) := by
  sorry

/-- The canonical ordinary evaluation comparison, fixed by the universal generator.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def inverseEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  (inverseEvaluation_existsUnique l E f n).choose

/-- Termwise scalar restriction of a whole complex of systems.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
abbrev restrictComplex (W : Scheme.{t}) :=
  (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)

/-- Restriction evaluation on complexes through the recorded functor equality.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def restrictEvaluation (W : Scheme.{t})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    ((restrictComplex l E W).obj C).asFunctor.obj (op n) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) :=
  (NatIso.mapHomologicalComplex
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) (.up ℤ)).app C

/-- The actual termwise-limit identification for a complex of strict towers.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def limitComplexIso (W : Scheme.{t})
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    limit I.asFunctor ≅
      (Functor.mapHomologicalComplex
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
        (.up ℤ)).obj I :=
  limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval I.asFunctor,
    HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor⟩

/-- The two existing Roos presentations are the same shifted product cone.
Source: Stacks 0941 (blueprint: lem-pur-completed-primitive-counit-comparison). -/
def roosBridge (W : Scheme.{t})
    (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
    integralOperationsRoosFunctor.obj Z.asFunctor ≅ roosF.obj Z := Iso.refl _

/-- One natural projection-compatible Roos realization, normalized on every resolution.
The actual inclusion roosι has zero shifted coordinate, as defined in StrictRoosModel.
Source: Stacks 0941 and lem-weil-strict-roos-comparison
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
structure RoosRealization (W : Scheme.{t}) where
  comparison : (roosF (A := scalarReductionSource l E W)) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E W
  projection : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ),
    comparison.hom.app Z ≫
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj Z) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app Z =
      DerivedCategory.Q.map (roosEval Z n)
  resolution : ∀ (Z I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (q : Z ⟶ I) [QuasiIso q] [I.IsKInjective],
    ∃ ι : DerivedCategory.Q.obj (limit I.asFunctor) ≅ DerivedCategory.Q.obj (roosF.obj I),
      ι.hom = DerivedCategory.Q.map (roosι I) ∧
      comparison.hom.app Z ≫
          (coefficientConstantTowerLimit l E W).map (DerivedCategory.Q.map q) =
        DerivedCategory.Q.map (roosF.map q) ≫ ι.inv ≫
          DerivedCategory.Q.map (limitComplexIso l E W I).hom ≫
          (Functor.rightDerivedFunctorObjQIso
            (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I).inv

/-- The tensor primitive arrow is realization followed by the image of both counits.
Source: the beta_T formula of the node; Stacks 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def tensorBeta (W : Scheme.{t}) (S : CoefficientDerivedSystemReduction l E W)
    (r : integralCompletedTensor l E W ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W)
    (A N : coefficientSequenceDerived l E W) :=
  r.hom.app ((coefficientSequenceLimit l E W).obj A,
    (coefficientSequenceLimit l E W).obj N) ≫
      (coefficientSequenceLimit l E W).map
        (S.systemClosed.tensor.map (Prod.mkHom (S.adjunction.counit.app A)
          (S.adjunction.counit.app N)))

/-- The geometric primitive arrow is realization followed by the image of the counit.
Source: the beta_F formula of the node; Stacks 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def pullBeta {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (r : integralDerivedPullback l E f ≅
      S.reduction ⋙ pull l E f ⋙ coefficientSequenceLimit l E X)
    (A : coefficientSequenceDerived l E Y) :=
  r.hom.app ((coefficientSequenceLimit l E Y).obj A) ≫
    (coefficientSequenceLimit l E X).map
      ((pull l E f).map (S.adjunction.counit.app A))

/-- The tensor representative comparison in the derived category of restricted towers.
Source: Stacks 07A4, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def tensorRestrictionIso (W : Scheme.{t}) (S : CoefficientDerivedSystemReduction l E W)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ)
    (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) D)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q) ≅ DerivedCategory.Q.obj D) :
    (coefficientSequenceDerivedRestriction l E W).obj
        (S.systemClosed.tensor.obj (S.reduction.obj (DerivedCategory.Q.obj P),
          S.reduction.obj (DerivedCategory.Q.obj Q))) ≅
      DerivedCategory.Q.obj ((restrictComplex l E W).obj
        ((coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (C, D))) :=
  (coefficientSequenceDerivedRestriction l E W).mapIso
      (S.systemClosed.tensor.mapIso (eC.prod eD) ≪≫
        (S.systemTensorModel.iso (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W) S.systemClosed C D hC hD).symm) ≪≫
    (coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app _

/-- The geometric representative comparison in the derived category of restricted towers.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def pullRestrictionIso {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj C) :
    (coefficientSequenceDerivedRestriction l E X).obj
        ((pull l E f).obj (S.reduction.obj (DerivedCategory.Q.obj P))) ≅
      DerivedCategory.Q.obj ((restrictComplex l E X).obj
        (((inverse l E f).mapHomologicalComplex (.up ℤ)).obj C)) :=
  (coefficientSequenceDerivedRestriction l E X).mapIso
      ((pull l E f).mapIso eC ≪≫ (inverse l E f).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app _

/-- The finite tensor presentation is the actual scalar restriction of the total tensor.
The map is the identity, retaining the recorded scalar extension and its quotient maps.
Source: Stacks 06YY, 07A4, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  Iso.refl _

/-- The complex inverse-image evaluation induced by the unit-normalized ordinary one.
Source: Stacks 03D3, 0941
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def inverseComplexEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    (inverse l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ) ≅
    (coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ) ⋙
      (integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ) :=
  by
    letI : (integralOperationsLevelPullback l E f n).Additive :=
      integralOperationsLevelPullback_additive l E f n
    exact (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)) ≪≫
      NatIso.mapHomologicalComplex (inverseEvaluation l E f n) (.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm

attribute [local irreducible] integralOperationsTensorLevel coefficientTotalTensor
  integralOperationsRoosFunctor

/-- Tensor realization on every good pair uses the prescribed strict quotient tower.
The component formula for z pins its pure tensors through the existing ordinary
coefficient evaluation comparison and the canonical finite tensor presentation.
Source: Stacks 0941, proof steps 1--3 of the node
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def TensorModel (W : Scheme.{t}) (S : CoefficientDerivedSystemReduction l E W)
    (ρ : RoosRealization l E W)
    (r : integralCompletedTensor l E W ≅
      S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W) :
    Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
    ∃ (C D : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (hC : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) C)
      (hD : CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) D)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (κD : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q.obj)
      (z : ((restrictComplex l E W).obj
        ((coefficientTotalTensor.{u, t+1, t}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (C, D))).asFunctor ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj)),
      CoefficientReductionPresentation l E W S P.obj P.property.1 C eC κC ∧
      CoefficientReductionPresentation l E W S Q.obj Q.property.1 D eD κD ∧
      (∀ n : ℕ, z.hom.app (op n) =
        (restrictEvaluation l E W _ n).hom ≫
          ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map
            ((coefficientEvaluationTensorIso l E W n C D).hom ≫
              (coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
                (integralCoefficientCommRingSheaf l E W n)).map
                  (Prod.mkHom (κC n).hom (κD n).hom)) ≫
          (finiteTensorBridge l E W n P.obj Q.obj).hom) ∧
      (integralCompletedTensorComparison l E W).hom.app (P, Q) ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.mapIso z.symm).hom ≫
          DerivedCategory.Q.map (roosBridge l E W _).hom =
        r.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (coefficientConstantTowerLimit l E W).map
            (tensorRestrictionIso l E W S P.obj Q.obj C D hC hD eC eD).hom ≫
          ρ.comparison.inv.app _

/-- Geometric realization on good representatives uses the actual pullback transitions.
Its strict tower comparison is fixed by the ordinary unit-normalized component maps.
Source: Stacks 0941, proof steps 1--3 of the node
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
def PullModel {X Y : Scheme.{t}} (f : X ⟶ Y)
    (S : CoefficientDerivedSystemReduction l E Y) (ρ : RoosRealization l E X)
    (r : integralDerivedPullback l E f ≅
      S.reduction ⋙ pull l E f ⋙ coefficientSequenceLimit l E X) : Prop :=
  ∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
    ∃ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
      (κC : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          ((scalarReductionExtension l E Y n).mapHomologicalComplex (.up ℤ)).obj P.obj)
      (z : ((restrictComplex l E X).obj
        (((inverse l E f).mapHomologicalComplex (.up ℤ)).obj C)).asFunctor ≅
          (integralOperationsPullbackTowerFunctor l E f).obj P.obj),
      CoefficientReductionPresentation l E Y S P.obj P.property.1 C eC κC ∧
      (∀ n : ℕ, z.hom.app (op n) =
        (restrictEvaluation l E X _ n).hom ≫
          ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
            ((inverseComplexEvaluation l E f n).hom.app C ≫
              ((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).map
                (κC n).hom)) ∧
      (integralDerivedPullbackComparison l E f).hom.app P ≫
          DerivedCategory.Q.map (integralOperationsRoosFunctor.mapIso z.symm).hom ≫
          DerivedCategory.Q.map (roosBridge l E X _).hom =
        r.hom.app (DerivedCategory.Q.obj P.obj) ≫
          (coefficientConstantTowerLimit l E X).map
            (pullRestrictionIso l E f S P.obj C eC).hom ≫ ρ.comparison.inv.app _

/-- Natural primitive comparisons, their strict representative normalizations and
inverse words, together with whole-system counit and actual projection naturality.
Source: Stacks 0941, proof steps 1--6 of the node
(blueprint: lem-pur-completed-primitive-counit-comparison). -/
structure Comparisons {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (S : CoefficientDerivedSystemReduction l E W)
    (V : CoefficientDerivedSystemReduction l E Y)
    (ρW : RoosRealization l E W) (ρX : RoosRealization l E X) where
  tensor : integralCompletedTensor l E W ≅
    S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit l E W
  geometric : integralDerivedPullback l E f ≅
    V.reduction ⋙ pull l E f ⋙ coefficientSequenceLimit l E X
  tensor_model : TensorModel l E W S ρW tensor
  geometric_model : PullModel l E f V ρX geometric
  geometric_evaluation : ∀ n : ℕ,
    Nonempty (pull l E f ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapDerivedCategory)
  counit_effective : ∀ A : coefficientSequenceDerived l E W,
    IsNormalizedCoefficientSequence l E W A → IsIso (S.adjunction.counit.app A)
  geometric_counit_effective : ∀ C : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y C → IsIso (V.adjunction.counit.app C)
  tensor_iso : ∀ A N : coefficientSequenceDerived l E W,
    IsNormalizedCoefficientSequence l E W A → IsNormalizedCoefficientSequence l E W N →
      IsIso (tensorBeta l E W S tensor A N)
  geometric_iso : ∀ C : coefficientSequenceDerived l E Y,
    IsNormalizedCoefficientSequence l E Y C → IsIso (pullBeta l E f V geometric C)
  tensor_inverse : ∀ (A N : coefficientSequenceDerived l E W)
    (_hA : IsNormalizedCoefficientSequence l E W A)
    (_hN : IsNormalizedCoefficientSequence l E W N)
    (eA : S.reduction.obj ((coefficientSequenceLimit l E W).obj A) ≅ A)
    (eN : S.reduction.obj ((coefficientSequenceLimit l E W).obj N) ≅ N)
    (_heA : eA.hom = S.adjunction.counit.app A)
    (_heN : eN.hom = S.adjunction.counit.app N),
    ∃ b : (integralCompletedTensor l E W).obj
        ((coefficientSequenceLimit l E W).obj A, (coefficientSequenceLimit l E W).obj N) ≅
        (coefficientSequenceLimit l E W).obj (S.systemClosed.tensor.obj (A, N)),
      b.hom = tensorBeta l E W S tensor A N ∧
      b.inv = (coefficientSequenceLimit l E W).map
        (S.systemClosed.tensor.map (Prod.mkHom eA.inv eN.inv)) ≫
          tensor.inv.app ((coefficientSequenceLimit l E W).obj A,
            (coefficientSequenceLimit l E W).obj N)
  geometric_inverse : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C)
    (eC : V.reduction.obj ((coefficientSequenceLimit l E Y).obj C) ≅ C)
    (_heC : eC.hom = V.adjunction.counit.app C),
    ∃ b : (integralDerivedPullback l E f).obj ((coefficientSequenceLimit l E Y).obj C) ≅
      (coefficientSequenceLimit l E X).obj ((pull l E f).obj C),
      b.hom = pullBeta l E f V geometric C ∧
      b.inv = (coefficientSequenceLimit l E X).map ((pull l E f).map eC.inv) ≫
        geometric.inv.app ((coefficientSequenceLimit l E Y).obj C)
  tensor_naturality : ∀ {A A' N N' : coefficientSequenceDerived l E W}
    (a : A ⟶ A') (b : N ⟶ N'),
    (integralCompletedTensor l E W).map
        (Prod.mkHom ((coefficientSequenceLimit l E W).map a)
          ((coefficientSequenceLimit l E W).map b)) ≫ tensorBeta l E W S tensor A' N' =
      tensorBeta l E W S tensor A N ≫
        (coefficientSequenceLimit l E W).map (S.systemClosed.tensor.map (Prod.mkHom a b))
  geometric_naturality : ∀ {C C' : coefficientSequenceDerived l E Y} (a : C ⟶ C'),
    (integralDerivedPullback l E f).map ((coefficientSequenceLimit l E Y).map a) ≫
        pullBeta l E f V geometric C' =
      pullBeta l E f V geometric C ≫
        (coefficientSequenceLimit l E X).map ((pull l E f).map a)
  counit_naturality : ∀ {A A' : coefficientSequenceDerived l E W} (a : A ⟶ A'),
    S.reduction.map ((coefficientSequenceLimit l E W).map a) ≫ S.adjunction.counit.app A' =
      S.adjunction.counit.app A ≫ a
  geometric_counit_naturality : ∀ {C C' : coefficientSequenceDerived l E Y} (a : C ⟶ C'),
    V.reduction.map ((coefficientSequenceLimit l E Y).map a) ≫ V.adjunction.counit.app C' =
      V.adjunction.counit.app C ≫ a
  projections : ∀ {A A' : coefficientSequenceDerived l E W} (a : A ⟶ A') (n : ℕ),
    (coefficientSequenceLimit l E W).map a ≫ (coefficientSequenceProjection l E W n).app A' =
      (coefficientSequenceProjection l E W n).app A ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceDerivedEvaluation l E W n).map a)
  geometric_projections : ∀ {C C' : coefficientSequenceDerived l E Y} (a : C ⟶ C') (n : ℕ),
    (coefficientSequenceLimit l E Y).map a ≫ (coefficientSequenceProjection l E Y n).app C' =
      (coefficientSequenceProjection l E Y n).app C ≫
        (coefficientFiniteDerivedRestriction l E Y n).map
          ((coefficientSequenceDerivedEvaluation l E Y n).map a)

end PrimitiveCounit

/-- Quotient-limit realization of completed tensor and pullback, with primitive
comparisons given by the coherent system counit. The calculus parameters provide
the dependency's canonical reduction and its tensor models, with no arbitrary maps.
Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
refined by lem-weil-strict-roos-comparison and the coefficient-system adjunction
(blueprint: lem-pur-completed-primitive-counit-comparison).

Proof, following every step of the node:
1. Choose flat-term K-flat representatives P,Q by lem-pc-kflat-resolution. Their
quotients are K-flat by lem-pur-kflat-change-of-rings. Componentwise exactness gives
K-flatness as whole systems. Their tensor and inverse image are the actual strict
quotient tensor and pullback towers, with the prescribed transitions on generators.
2. Restrict to completed-coefficient towers. Countable products are exact by
lem-weil-proetale-countable-products-exact. Apply lem-weil-strict-roos-comparison:
on a K-injective tower resolution q the map is C(q) followed by the inverse of
the inclusion lim I to C(I) with zero shifted coordinate. It preserves projections.
3. Compose with the representative comparisons of lem-pur-integral-operations-well-defined.
Naturality on strict maps and inversion of quasi-isomorphisms descend to natural
functor isomorphisms. Unique-compatible descent makes them resolution independent.
4. The evaluation-calculus adjunction supplies one whole-system counit. Effectivity
makes its finite evaluations invertible on normalized systems; joint conservativity
makes the whole counit invertible. Its naturality holds for all whole-system maps.
5. Apply tensor or inverse image to these counit isomorphisms, then total limit,
and precompose with realization. Functoriality cancels each counit with its inverse
in both orders, giving exactly the displayed inverse formulas.
6. Apply tensor or inverse image to the whole-system counit naturality equation,
then limit and realization naturality. Actual limit projections are natural on
resolutions, and Roos preserves their equations. Their scalar-extension adjoints
are the evaluated counits by the evaluation calculus. No equality of derived maps
is inferred just from their evaluations. Zero objects, empty schemes and identity
morphisms are included; n=0 denotes exponent one throughout. -/
theorem completedPrimitiveCounitComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{t}} (f : X ⟶ Y) (W : Scheme.{t})
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (S : CoefficientDerivedSystemReduction l E W)
    (V : CoefficientDerivedSystemReduction l E Y) :
    ∃ (ρW : PrimitiveCounit.RoosRealization l E W)
      (ρX : PrimitiveCounit.RoosRealization l E X),
      Nonempty (PrimitiveCounit.Comparisons l E f W S V ρW ρX) := by
  sorry

end WeilConjectures
