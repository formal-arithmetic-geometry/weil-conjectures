/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.CoefficientRingedSequenceSite
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntegralScalarExtensionWellDefined
import Sheaf.CategoryTheory.SystemScalarCoherence
import Sheaf.CategoryTheory.SystemScalarGenerators
import Sheaf.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Sheaf.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Sheaf.Algebra.Homology.SheafRingDerivedHomComparison
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.CategoryTheory.ContinuousModulePullbackKFlat
import Sheaf.CategoryTheory.DerivedCategory.ResolvingScalarSquare
import all Sheaf.Paper.ReductionPullbackDerivedTower
import Sheaf.CategoryTheory.VerticalEvaluationInverseMate
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
/-!
# Realization of integral pullback comparisons

Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: def-trf-integral-comparison-sequence-systems).

The sequence site retains the whole quotient diagram. Its pullback is the left
adjoint of the actual sectionwise direct image. Scalar change is the universal
derived change of rings for the actual map of quotient coefficient sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped ChangeOfRings

/-- Base change on the actual sequence site. Source: Stacks 0941, 09A5
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceBaseChange {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (ℕ × Y.ProEt) ⥤ (ℕ × X.ProEt) :=
  (𝟭 ℕ).prod (proEtaleBaseChange f)

/-- Base change is continuous on the sequence site. Source: Stacks 0941, 09A5
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: a covering is a vertical covering at its index. Base change preserves the
vertical covering, by continuity on the small pro-etale site. Thus the restriction
of a sheaf is a sheaf, which is exactly the asserted continuity. -/
theorem integralComparisonSequenceBaseChange_continuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceBaseChange f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) := by
  have : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  have : RepresentablyFlat (integralComparisonSequenceBaseChange f) := by
    constructor
    intro A
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence A.1 A.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  apply Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
  constructor
  intro A S hS
  change (S.functorPushforward (integralComparisonSequenceBaseChange f)).functorPullback
    (Prod.sectR A.1 X.ProEt) ∈ ProEt.topology X _
  apply (ProEt.topology X).superset_covering _
    ((proEtaleBaseChangeCoverPreserving f).cover_preserve hS)
  rintro V a ⟨W, b, c, hb, rfl⟩
  exact ⟨(A.1, W), Prod.mkHom (𝟙 A.1) b, Prod.mkHom (𝟙 A.1) c, hb, rfl⟩

/-- Continuity of the actual sequence-site base change. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequenceBaseChangeContinuous {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceBaseChange f).IsContinuous
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) :=
  integralComparisonSequenceBaseChange_continuous f

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The component of the constant-section map on the product site.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceRingComponent {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : (ℕ × Y.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingPresheaf l E Y).obj A ⟶
      (coefficientSequenceCommRingPresheaf l E X).obj
        ((integralComparisonSequenceBaseChange f).op.obj A) :=
  (coefficientProEtaleDirectRingMap.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (A.unop.1 + 1))))).hom.app (op A.unop.2)

private theorem sequenceConstantUnit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{t, u} f A).hom.app U =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange f).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem sequenceConstantMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
      coefficientProEtaleDirectRingMap.{t, u} f B =
    coefficientProEtaleDirectRingMap.{t, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj B)) |>.injective
  apply NatTrans.ext
  funext U
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  have hY := congrArg (fun α ↦ α.app U)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at hY
  erw [← Category.assoc, ← hY, Category.assoc, sequenceConstantUnit,
    ← Category.assoc, sequenceConstantUnit]
  exact congrArg (fun α ↦ α.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

/-- The constant-section coefficient maps commute with horizontal quotients and
vertical restrictions. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: on constant sections both composites send a residue class to the same
constant section at the smaller exponent. Sheafification gives horizontal
naturality. Naturality of each coefficient map gives vertical naturality. Every
arrow in the product site factors into a horizontal and a vertical arrow. -/
theorem integralComparisonSequenceRing_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : (ℕ × Y.ProEt)ᵒᵖ} (g : A ⟶ B) :
    (coefficientSequenceCommRingPresheaf l E Y).map g ≫
        integralComparisonSequenceRingComponent l E f B =
      integralComparisonSequenceRingComponent l E f A ≫
        (coefficientSequenceCommRingPresheaf l E X).map
          ((integralComparisonSequenceBaseChange f).op.map g) := by
  let τ : coefficientSequenceCommRingSystem l E Y ⟶
      coefficientSequenceCommRingSystem l E X ⋙
        (proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X) :=
    NatTrans.ofOpSequence (fun n ↦ coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))) (fun n ↦ by
      simp only [coefficientSequenceCommRingSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact sequenceConstantMap_naturality f
        (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift))
  exact (Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := Y.ProEt)).functor
    (Functor.uncurry.map (Functor.whiskerRight τ
      (sheafToPresheaf (ProEt.topology Y) CommRingCat)))).naturality g

/-- Actual constant coefficients on the sequence site, with their quotient transitions.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceRingMap {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSheaf l E Y ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          (coefficientSequenceCommRingSheaf l E X) where
  hom :=
    { app := integralComparisonSequenceRingComponent l E f
      naturality := fun {_ _} g ↦ integralComparisonSequenceRing_naturality l E f g }

/-- Sectionwise direct image with the prescribed quotient coefficient action.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceDirectImage {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceModules l E X ⥤ coefficientSequenceModules l E Y :=
  SheafOfModules.pushforward.{max u (t + 1)}
    (F := integralComparisonSequenceBaseChange f)
    (J := coefficientSequenceTopology (ProEt.topology Y))
    (K := coefficientSequenceTopology (ProEt.topology X))
    (S := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E Y))
    (R := (sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
      RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E X))
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The ordinary system inverse image exists. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: module sheaves on the sequence site form a Grothendieck abelian category,
so they have a small coseparating family and are complete and well-powered.
Direct image preserves limits: after evaluation it is evaluation on the source
followed by restriction of scalars, both of which preserve limits. Evaluation
jointly reflects limits. The special adjoint functor theorem supplies the left
adjoint, with the original independent scheme and coefficient universes. -/
theorem integralComparisonSequenceDirectImage_isRightAdjoint
    {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).IsRightAdjoint := by
  have : IsGrothendieckAbelian.{max u (t + 1)}
      (coefficientSequenceModules l E X) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses _ _
  have : PreservesLimitsOfSize.{max u (t + 1), max u (t + 1)}
      (integralComparisonSequenceDirectImage l E f) := by
    constructor
    intro J _
    have : Small.{max u (t + 1)} J := inferInstance
    constructor
    intro K
    constructor
    intro c hc
    refine ⟨?_⟩
    apply isLimitOfReflects (SheafOfModules.forget _)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    change IsLimit ((ModuleCat.restrictScalars
      ((Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
        (forget₂ CommRingCat RingCat)).app U).hom).mapCone
          ((SheafOfModules.evaluation _
            ((integralComparisonSequenceBaseChange f).op.obj U)).mapCone c))
    have he : PreservesLimit K (SheafOfModules.evaluation _
        ((integralComparisonSequenceBaseChange f).op.obj U)) := inferInstance
    exact isLimitOfPreserves _ (isLimitOfPreserves _ hc)
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating
    (isCoseparator_coseparator (coefficientSequenceModules l E X)) _

/-- The adjunction structure whose right side is the actual sectionwise direct image.
Source: Stacks 03D2 (blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequenceRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).IsRightAdjoint :=
  integralComparisonSequenceDirectImage_isRightAdjoint l E f

/-- The canonical ordinary inverse image of strict quotient systems.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequencePullback {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (integralComparisonSequenceDirectImage l E f).leftAdjoint

private theorem sequencePullbackEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    Nonempty (integralComparisonSequencePullback l E f ⋙
      coefficientSequenceEvaluation l E X n ≅ coefficientSequenceEvaluation l E Y n ⋙
        coefficientProEtaleModulePullback.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))) := by
  let adj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let adjn := coefficientProEtaleModuleAdjunction.{t, u} f
    (CommRingCat.of (ULift.{t + 1}
      (Padic.coefficientExtensionRing l E (n + 1))))
  let ρ : (sheafCompose (coefficientSequenceTopology (ProEt.topology Y))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        (coefficientSequenceCommRingSheaf l E Y) ⟶
      ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous
        RingCat.{max u (t + 1)} (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceTopology (ProEt.topology X))).obj
            ((sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)}
              RingCat.{max u (t + 1)})).obj (coefficientSequenceCommRingSheaf l E X)) :=
    ⟨Functor.whiskerRight (integralComparisonSequenceRingMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  let φ := eqToHom (coefficientSequenceEvaluationRing_eq l E Y n).symm
  let ψ := eqToHom (coefficientSequenceEvaluationRing_eq l E X n).symm
  let σ := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
      (coefficientProEtaleDirectRingMap.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))))
  have h := CategoryTheory.VerticalEvaluation.pushforwardEvaluation.{t + 1, t, u}
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f) _ _ n _ _ φ ψ ρ σ (by
      intro U
      have hφ : φ.hom.app U = 𝟙 _ := by
        dsimp only [φ]
        rw [ObjectProperty.eqToHom_hom, eqToHom_app]
        rfl
      have hψ : ψ.hom.app ((proEtaleBaseChange f).op.obj U) = 𝟙 _ := by
        dsimp only [ψ]
        rw [ObjectProperty.eqToHom_hom, eqToHom_app]
        rfl
      rw [hφ, hψ]
      erw [Category.id_comp])
  let e := h.choose
  have hi := CategoryTheory.VerticalEvaluation.inverseMateFor_isIso.{t + 1, t, u}
    (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f) _ _ n ρ _ _
    (coefficientSequenceEvaluationRing_eq l E Y n)
    (coefficientSequenceEvaluationRing_eq l E X n) σ _ adj _ adjn e h.choose_spec
  exact ⟨(asIso ((mateEquiv adj adjn).symm e.hom).natTrans).symm⟩

/-- Exactness of constant-coefficient system inverse image. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: evaluate at each positive exponent. The unit-normalized inverse-image
adjunction is the finite constant-coefficient adjunction, which is exact.
Kernels, cokernels and addition in the system category are levelwise. -/
theorem integralComparisonSequencePullback_exact {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequencePullback l E f).Additive ∧
      PreservesFiniteLimits (integralComparisonSequencePullback l E f) ∧
      PreservesFiniteColimits (integralComparisonSequencePullback l E f) := by
  let F := integralComparisonSequencePullback l E f
  let adj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  have : (integralComparisonSequenceDirectImage l E f).Additive := by
    constructor
    intro M N g h
    ext U x
    rfl
  have : F.Additive := adj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  have hEv (n : ℕ) : PreservesFiniteLimits (F ⋙ coefficientSequenceEvaluation l E X n) := by
    obtain ⟨e⟩ := sequencePullbackEvaluation l E f n
    have hex := coefficientProEtaleModulePullback_exact.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))
    have := hex.1
    exact preservesFiniteLimits_of_natIso e.symm
  have : F.PreservesMonomorphisms := by
    constructor
    intro M N g hg
    constructor
    intro T a b hab
    ext U x
    have hn := hEv U.unop.1
    have : Mono ((coefficientSequenceEvaluation l E X U.unop.1).map (F.map g)) :=
      (F ⋙ coefficientSequenceEvaluation l E X U.unop.1).map_mono g
    have he : (coefficientSequenceEvaluation l E X U.unop.1).map a =
        (coefficientSequenceEvaluation l E X U.unop.1).map b := by
      apply (cancel_mono
        ((coefficientSequenceEvaluation l E X U.unop.1).map (F.map g))).1
      simpa only [← Functor.map_comp] using
        congrArg (coefficientSequenceEvaluation l E X U.unop.1).map hab
    exact congrArg (fun f ↦ f.val.app (op U.unop.2) x) he
  have : F.PreservesHomology := F.preservesHomology_of_preservesMonos_and_cokernels
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Additivity of system inverse image. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequencePullbackAdditive {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequencePullback l E f).Additive :=
  (integralComparisonSequencePullback_exact l E f).1

/-- Finite limits are computed levelwise. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequencePullbackLimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteLimits (integralComparisonSequencePullback l E f) :=
  (integralComparisonSequencePullback_exact l E f).2.1

/-- Finite colimits are computed levelwise. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
instance integralComparisonSequencePullbackColimits {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PreservesFiniteColimits (integralComparisonSequencePullback l E f) :=
  (integralComparisonSequencePullback_exact l E f).2.2

/-- Exact inverse image on the derived category of entire strict quotient systems.
Source: Stacks 0941, 0D6D
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonDerivedSequencePullback {X Y : Scheme.{t}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E Y ⥤ coefficientSequenceDerived l E X :=
  (integralComparisonSequencePullback l E f).mapDerivedCategory


variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Inclusion of the actual quotient rings on the sequence site.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarComponent (X : Scheme.{t}) (A : (ℕ × X.ProEt)ᵒᵖ) :
    (coefficientSequenceCommRingPresheaf l E X).obj A ⟶
      (coefficientSequenceCommRingPresheaf l L X).obj A :=
  (integralScalarQuotientSheafMap l E L ι X A.unop.1).hom.app (op A.unop.2)

/-- Quotient coefficient inclusions are natural on the entire sequence site.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: the horizontal square is integralScalarQuotientMap_transition. The vertical
square is naturality of constant sheafification. Factor a product-site arrow into
these two arrows and paste the squares. -/
theorem integralComparisonSequenceScalar_naturality (X : Scheme.{t})
    {A B : (ℕ × X.ProEt)ᵒᵖ} (g : A ⟶ B) :
    (coefficientSequenceCommRingPresheaf l E X).map g ≫
        integralComparisonSequenceScalarComponent l E L ι X B =
      integralComparisonSequenceScalarComponent l E L ι X A ≫
        (coefficientSequenceCommRingPresheaf l L X).map g := by
  let τ : coefficientSequenceCommRingSystem l E X ⟶
      coefficientSequenceCommRingSystem l L X :=
    NatTrans.ofOpSequence (integralScalarQuotientSheafMap l E L ι X) (fun n ↦ by
      simp only [coefficientSequenceCommRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map
          (CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift) ≫
          integralScalarQuotientSheafMap l E L ι X n =
        integralScalarQuotientSheafMap l E L ι X (n + 1) ≫
          (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map
            (CommRingCat.ofHom (Padic.coefficientExtensionTransition l L (n + 1)).ulift)
      unfold integralScalarQuotientSheafMap
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      ext x
      exact congrArg (fun q ↦ q x.down)
        (integralScalarQuotientMap_transition l E L ι n).symm)
  exact (Functor.whiskerLeft (prodOpEquiv (C := ℕ) (D := X.ProEt)).functor
    (Functor.uncurry.map (Functor.whiskerRight τ
      (sheafToPresheaf (ProEt.topology X) CommRingCat)))).naturality g

/-- The specified morphism of quotient coefficient sheaves, before deriving.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarMap (X : Scheme.{t}) :
    coefficientSequenceCommRingSheaf l E X ⟶ coefficientSequenceCommRingSheaf l L X where
  hom :=
    { app := integralComparisonSequenceScalarComponent l E L ι X
      naturality := fun {_ _} g ↦ integralComparisonSequenceScalar_naturality l E L ι X g }

/-- The universal, cochain-normalized derived coefficient change on the sequence site.
The universal counit determines the pair up to the unique compatible isomorphism.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarModel (X : Scheme.{t}) :=
  Classical.choice (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
    (integralComparisonSequenceScalarMap l E L ι X))

attribute [local irreducible] integralComparisonSequenceScalarModel

/-- Derived scalar extension of whole strict coefficient systems, retaining homotopies.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonDerivedSequenceScalar (X : Scheme.{t}) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l L X :=
  (integralComparisonSequenceScalarModel l E L ι X).T

private theorem sequenceScalarAdjunction (X : Scheme.{t}) :
    ∃ adj : (integralComparisonSequenceScalarModel l E L ι X).E ⊣
      SheafOfModules.restrictScalars ((sheafCompose
        (coefficientSequenceTopology (ProEt.topology X)) (forget₂ CommRingCat RingCat)).map
          (integralComparisonSequenceScalarMap l E L ι X)),
      ∀ (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
        (x : N.val.obj U),
        (adj.unit.app N).val.app U x =
          (eqToHom ((integralComparisonSequenceScalarModel l E L ι X).obj_eq N).symm).val.app U
            ((toSheafify (coefficientSequenceTopology (ProEt.topology X))
              (SheafOfModules.changeOfRingsPresheaf
                (integralComparisonSequenceScalarMap l E L ι X) N).presheaf).app U
                  ((1 : (coefficientSequenceCommRingSheaf l L X).obj.obj U)
                    ⊗ₜ[(coefficientSequenceCommRingSheaf l E X).obj.obj U,
                      ((integralComparisonSequenceScalarMap l E L ι X).hom.app U).hom] x)) := by
  exact SheafOfModules.ScalarReductionProof.tensorAdjunction_of_identifications
    (integralComparisonSequenceScalarMap l E L ι X)
    (integralComparisonSequenceScalarModel l E L ι X).E
    (integralComparisonSequenceScalarModel l E L ι X).obj_eq
    (integralComparisonSequenceScalarModel l E L ι X).map_eq

private noncomputable abbrev sequenceScalarPackage (X : Scheme.{t}) :
    SheafOfModules.SystemScalarModel.{t + 1, t, max u (t + 1)}
      (integralComparisonSequenceScalarMap l E L ι X) := by
  let D := integralComparisonSequenceScalarModel l E L ι X
  let h := exists_homotopy_leftDerived_comparison D.E D.T D.ε D.universal
  let ε := h.choose
  have hε := h.choose_spec.1
  have hεP := h.choose_spec.2
  let ho := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (integralComparisonSequenceScalarMap l E L ι X)
  let h := ho.choose_spec.choose_spec D.E D.obj_eq D.map_eq
  let a := h.choose
  have ha := h.choose_spec
  let h := SheafOfModules.sheafRingDerivedHomComparison
    (integralComparisonSequenceScalarMap l E L ι X)
    D.E D.obj_eq D.map_eq a D.T ε hε
  let d := h.choose
  have hd := h.choose_spec
  refine { model := D
           ordinaryAdj := a
           unit_normalized := ?_
           adjunction := d
           transpose := adjunction_cochain_transpose
             D.E _ a D.T D.ε ε hεP d hd }
  intro P U x
  have hu := ha P (D.E.obj P) (eqToHom (D.obj_eq P).symm) U x
  dsimp only [SheafOfModules.systemModelTmul]
  rw [one_smul]
  simp only [eqToHom_trans, eqToHom_refl, Adjunction.homEquiv_id] at hu
  exact hu

/-- The system pullback generator is the actual adjunction unit on sections.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceGenerator {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :=
  (((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).unit.app M).val.app (op (n, U))) x

private instance sequenceBaseCompContinuous {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).IsContinuous
      (ProEt.topology V) (ProEt.topology Z) := by
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ k).IsContinuous
      (ProEt.topology V) (ProEt.topology W) := proEtaleBaseChange_isContinuous k
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).IsContinuous
      (ProEt.topology W) (ProEt.topology Z) := proEtaleBaseChange_isContinuous h
  exact Functor.isContinuous_comp _ _ _ (ProEt.topology W) _

private instance sequenceBaseCompContinuous' {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    (proEtaleBaseChange k ⋙ proEtaleBaseChange h).IsContinuous
      (ProEt.topology V) (ProEt.topology Z) := sequenceBaseCompContinuous h k

private theorem sequenceConstantComp {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V)
    (A : CommRingCat.{max u (t + 1)}) :
    letI := sequenceBaseCompContinuous h k
    coefficientProEtaleDirectRingMap.{t, u} k A ≫
        ((proEtaleBaseChange k).sheafPushforwardContinuous _
          (ProEt.topology V) (ProEt.topology W)).map
          (coefficientProEtaleDirectRingMap.{t, u} h A) ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (F := proEtaleBaseChange (h ≫ k))
          (F' := proEtaleBaseChange k ⋙ proEtaleBaseChange h)
          (MorphismProperty.Over.pullbackComp h k).hom _
          (ProEt.topology V) (ProEt.topology Z)).app
            ((constantSheaf (ProEt.topology Z) CommRingCat.{max u (t + 1)}).obj A) =
      coefficientProEtaleDirectRingMap.{t, u} (h ≫ k) A := by
  apply ((sheafificationAdjunction (ProEt.topology V) CommRingCat.{max u (t + 1)}).homEquiv
    ((Functor.const V.ProEtᵒᵖ).obj A) _).injective
  apply NatTrans.ext
  funext U
  change (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app U ≫
      ((coefficientProEtaleDirectRingMap k A).hom.app U ≫
        (coefficientProEtaleDirectRingMap h A).hom.app ((proEtaleBaseChange k).op.obj U)) ≫
      ((constantSheaf (ProEt.topology Z) CommRingCat.{max u (t + 1)}).obj A).obj.map
        ((MorphismProperty.Over.pullbackComp h k).hom.app U.unop).op =
    (toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap (h ≫ k) A).hom.app U
  rw [← Category.assoc, ← Category.assoc, sequenceConstantUnit,
    sequenceConstantUnit, sequenceConstantUnit]
  have hn := (toSheafify (ProEt.topology Z)
    ((Functor.const Z.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp h k).hom.app U.unop).op
  change 𝟙 A ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  exact hn.symm

private instance sequenceSystemCompContinuous {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    (integralComparisonSequenceBaseChange k ⋙
      integralComparisonSequenceBaseChange h).IsContinuous
        (coefficientSequenceTopology (ProEt.topology V))
        (coefficientSequenceTopology (ProEt.topology Z)) :=
  Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (ProEt.topology W)) _

private theorem sequenceRingVertical (W : Scheme.{t}) (n : ℕ)
    {U V : W.ProEt} (f : U ⟶ V) :
    (coefficientSequenceCommRingPresheaf l E W).map (Prod.mkHom (𝟙 n) f).op =
      ((constantSheaf (ProEt.topology W) CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).obj.map f.op := by
  change ((coefficientSequenceCommRingSystem l E W).map (𝟙 (op n))).hom.app (op V) ≫
    _ = _
  erw [(coefficientSequenceCommRingSystem l E W).map_id]
  rfl

private noncomputable def sequenceDirectComp {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    integralComparisonSequenceDirectImage l E h ⋙
      integralComparisonSequenceDirectImage l E k ≅
        integralComparisonSequenceDirectImage l E (h ≫ k) := by
  let e : integralComparisonSequenceBaseChange (h ≫ k) ≅
      integralComparisonSequenceBaseChange k ⋙ integralComparisonSequenceBaseChange h :=
    NatIso.prod (Iso.refl _) (MorphismProperty.Over.pullbackComp h k)
  exact SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ e (by
      ext U x
      let A := CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (U.unop.1 + 1)))
      change (coefficientSequenceCommRingPresheaf l E Z).map
        (Prod.mkHom (𝟙 U.unop.1)
          ((MorphismProperty.Over.pullbackComp h k).hom.app U.unop.2)).op
        ((coefficientProEtaleDirectRingMap h A).hom.app
          ((proEtaleBaseChange k).op.obj (op U.unop.2))
          ((coefficientProEtaleDirectRingMap k A).hom.app (op U.unop.2) x)) =
        (coefficientProEtaleDirectRingMap (h ≫ k) A).hom.app (op U.unop.2) x
      rw [sequenceRingVertical]
      exact congrArg (fun α ↦ α.hom.app (op U.unop.2) x) (sequenceConstantComp h k A))


/-- The ordinary compositor is determined by fibre-product pasting and mates.
Source: Stacks 0D6D, 03D3
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: direct images compose by the displayed sectionwise fibre-product map.
The coefficient actions agree because both send constant sections to themselves.
This gives the unique d. Take its mate under the actual adjunctions; mates
preserve isomorphisms and their bijection proves uniqueness of a. -/
theorem integralComparisonSequenceComposition_existsUnique
    {V W Z : Scheme.{t}} (h : Z ⟶ W) (k : W ⟶ V) :
    ∃! a : integralComparisonSequencePullback l E (h ≫ k) ≅
      integralComparisonSequencePullback l E k ⋙ integralComparisonSequencePullback l E h,
      ∃ d : integralComparisonSequenceDirectImage l E h ⋙
          integralComparisonSequenceDirectImage l E k ≅
            integralComparisonSequenceDirectImage l E (h ≫ k),
        conjugateIsoEquiv
          ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
            (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
          (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))) a = d ∧
        ∀ (M : coefficientSequenceModules l E Z) (n : ℕ) (U : V.ProEt)
          (x : ((integralComparisonSequenceDirectImage l E h ⋙
            integralComparisonSequenceDirectImage l E k).obj M).val.obj (op (n, U))),
          (d.hom.app M).val.app (op (n, U)) x =
            M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
              ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op x := by
  let adj := (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
  let adj' := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))
  let d := sequenceDirectComp l E h k
  refine ⟨(conjugateIsoEquiv adj adj').symm d, ⟨d, ?_, ?_⟩, ?_⟩
  · exact (conjugateIsoEquiv adj adj').apply_symm_apply d
  · intro M n U x
    rfl
  · rintro a ⟨d', ha, hd'⟩
    apply (conjugateIsoEquiv adj adj').injective
    rw [ha, Equiv.apply_symm_apply]
    apply Iso.ext
    ext M U x
    exact (hd' M U.unop.1 U.unop.2 x).trans (by rfl)


/-- The canonical ordinary composition map, retaining every quotient transition.
Source: Stacks 0D6D (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceComposition {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :=
  (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose

/-- Derived composition is the localization of that one strict system map.
Source: Stacks 0D6D, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemComposition {V W Z : Scheme.{t}}
    (h : Z ⟶ W) (k : W ⟶ V) :
    integralComparisonDerivedSequencePullback l E (h ≫ k) ≅
      integralComparisonDerivedSequencePullback l E k ⋙
        integralComparisonDerivedSequencePullback l E h :=
  Functor.mapDerivedCategoryNatIso (integralComparisonSequenceComposition l E h k) ≪≫
    Functor.mapDerivedCategoryCompIso (integralComparisonSequencePullback l E k)
      (integralComparisonSequencePullback l E h)

/-- An actual scalar-unit section in sequence-site change of rings.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceTensorSection (Y : Scheme.{t})
    (M : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : M.val.obj U) :
    ((integralComparisonSequenceScalarModel l E L ι Y).E.obj M).val.obj U :=
  (eqToHom ((integralComparisonSequenceScalarModel l E L ι Y).obj_eq M).symm).val.app U
    ((toSheafify (coefficientSequenceTopology (ProEt.topology Y))
      (SheafOfModules.changeOfRingsPresheaf
        (integralComparisonSequenceScalarMap l E L ι Y) M).presheaf).app U
          (s ⊗ₜ[(coefficientSequenceCommRingSheaf l E Y).obj.obj U,
            ((integralComparisonSequenceScalarMap l E L ι Y).hom.app U).hom] x))

private theorem sequenceTensorSection_smul (Y : Scheme.{t})
    (N : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : N.val.obj U) :
    integralComparisonSequenceTensorSection l E L ι Y N U s x =
      s • integralComparisonSequenceTensorSection l E L ι Y N U 1 x := by
  let η := (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)}
    (𝟙 ((sheafCompose (coefficientSequenceTopology (ProEt.topology Y))
      (forget₂ CommRingCat RingCat)).obj (coefficientSequenceCommRingSheaf l L Y)).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, max u (t + 1)}
        (integralComparisonSequenceScalarMap l E L ι Y) N)
  change (eqToHom ((integralComparisonSequenceScalarModel l E L ι Y).obj_eq N).symm).val.app U
      (η.app U (s ⊗ₜ[(coefficientSequenceCommRingSheaf l E Y).obj.obj U,
        ((integralComparisonSequenceScalarMap l E L ι Y).hom.app U).hom] x)) =
    s • (eqToHom ((integralComparisonSequenceScalarModel l E L ι Y).obj_eq N).symm).val.app U
      (η.app U ((1 : (coefficientSequenceCommRingSheaf l L Y).obj.obj U)
        ⊗ₜ[(coefficientSequenceCommRingSheaf l E Y).obj.obj U,
          ((integralComparisonSequenceScalarMap l E L ι Y).hom.app U).hom] x))
  rw [← ((eqToHom
    ((integralComparisonSequenceScalarModel l E L ι Y).obj_eq N).symm).val.app U).hom.map_smul]
  rw [← (η.app U).hom.map_smul]
  congr 2
  change (s ⊗ₜ[(coefficientSequenceCommRingSheaf l E Y).obj.obj U,
    ((integralComparisonSequenceScalarMap l E L ι Y).hom.app U).hom] x) =
    ((s * 1) ⊗ₜ[(coefficientSequenceCommRingSheaf l E Y).obj.obj U,
      ((integralComparisonSequenceScalarMap l E L ι Y).hom.app U).hom] x)
  rw [mul_one]


private theorem sequenceTensorSection_eq (Y : Scheme.{t})
    (N : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : N.val.obj U) :
    integralComparisonSequenceTensorSection l E L ι Y N U s x =
      SheafOfModules.systemModelTmul (integralComparisonSequenceScalarModel l E L ι Y)
        N U s x := by
  rw [sequenceTensorSection_smul]
  rfl

private theorem sequenceScalarPullbackRing {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    integralComparisonSequenceRingMap l E f ≫
        ((integralComparisonSequenceBaseChange f).sheafPushforwardContinuous _
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceTopology (ProEt.topology Z))).map
            (integralComparisonSequenceScalarMap l E L ι Z) =
      integralComparisonSequenceScalarMap l E L ι Y ≫
        integralComparisonSequenceRingMap l L f := by
  ext U : 3
  exact congrArg (fun α ↦ α.hom.app (op U.unop.2))
    (sequenceConstantMap_naturality f (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E L ι U.unop.1).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))).symm

private theorem sequenceScalarAdjunction_unit (X : Scheme.{t})
    (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ) (x : N.val.obj U) :
    (((sequenceScalarAdjunction l E L ι X).choose.unit.app N).val.app U x) =
      integralComparisonSequenceTensorSection l E L ι X N U 1 x :=
  (sequenceScalarAdjunction l E L ι X).choose_spec N U x

attribute [local irreducible] integralComparisonSequenceTensorSection

private noncomputable def sequenceScalarPullbackRight {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    SheafOfModules.restrictScalars ((sheafCompose
      (coefficientSequenceTopology (ProEt.topology Z)) (forget₂ CommRingCat RingCat)).map
        (integralComparisonSequenceScalarMap l E L ι Z)) ⋙
          integralComparisonSequenceDirectImage l E f ≅
      integralComparisonSequenceDirectImage l L f ⋙
        SheafOfModules.restrictScalars ((sheafCompose
          (coefficientSequenceTopology (ProEt.topology Y)) (forget₂ CommRingCat RingCat)).map
            (integralComparisonSequenceScalarMap l E L ι Y)) := by
  refine NatIso.ofComponents (fun N ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_)) ?_
  · intro r
    ext x
    have hr := congrArg (fun α ↦ α.hom.app U r)
      (sequenceScalarPullbackRing l E L ι f)
    change _ = _
    exact congrArg (fun s : (coefficientSequenceCommRingSheaf l L Z).obj.obj
      ((integralComparisonSequenceBaseChange f).op.obj U) ↦
        s • (show N.val.obj ((integralComparisonSequenceBaseChange f).op.obj U) from x)) hr.symm
  · intros
    ext x
    rfl
  · intros
    ext U x
    rfl

private theorem normalizedAdjointComparison
    {A B : Type*} [Category A] [Category B]
    (F G : A ⥤ B) (R T : B ⥤ A)
    (adj₁ : F ⊣ R) (adj₂ : G ⊣ T) (e : R ≅ T) :
    ∃! a : F ≅ G, ∀ X,
      adj₂.unit.app X ≫ e.inv.app (G.obj X) =
        adj₁.unit.app X ≫ R.map (a.hom.app X) := by
  let a := (conjugateIsoEquiv adj₂ adj₁).symm e.symm
  refine ⟨a, fun X ↦ unit_conjugateEquiv_symm adj₂ adj₁ e.inv X, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (adj₁.homEquiv X _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (hb X).symm.trans (unit_conjugateEquiv_symm adj₂ adj₁ e.inv X)

private theorem sequenceScalarPullbackRight_inv_app {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (N : coefficientSequenceModules l L Z) (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : N.val.obj ((integralComparisonSequenceBaseChange f).op.obj U)) :
    ((sequenceScalarPullbackRight l E L ι f).inv.app N).val.app U x = x := by
  rfl

attribute [local irreducible] sequenceScalarPullbackRight

/-- The ordinary scalar/pullback associator of whole quotient diagrams is fixed
on adjunction-unit tensor generators. Source: Stacks 06YY, 03D3
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: both functors sheafify the same scalar-balanced generators. Send the
specified unit tensor to the specified pullback of the unit tensor; multiply
scalars for the inverse. These formulas commute with vertical restrictions and
horizontal quotients, and local tensor generators prove uniqueness. -/
theorem integralComparisonSequenceScalarPullback_existsUnique
    {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    ∃! a : integralComparisonSequencePullback l E f ⋙
        (integralComparisonSequenceScalarModel l E L ι Z).E ≅
      (integralComparisonSequenceScalarModel l E L ι Y).E ⋙
        integralComparisonSequencePullback l L f,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
        (x : M.val.obj (op (n, U))),
      (a.hom.app M).val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι Z
          ((integralComparisonSequencePullback l E f).obj M)
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f M n U x)) =
        integralComparisonSequenceGenerator l L f
          ((integralComparisonSequenceScalarModel l E L ι Y).E.obj M) n U
          (integralComparisonSequenceTensorSection l E L ι Y M (op (n, U)) 1 x) := by
  let adjY := (sequenceScalarAdjunction l E L ι Y).choose
  have hY := sequenceScalarAdjunction_unit l E L ι Y
  let adjZ := (sequenceScalarAdjunction l E L ι Z).choose
  have hZ := sequenceScalarAdjunction_unit l E L ι Z
  let pE := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let pL := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l L f)
  let adj₁ := pE.comp adjZ
  let adj₂ := adjY.comp pL
  let e := sequenceScalarPullbackRight l E L ι f
  let h := normalizedAdjointComparison _ _ _ _ adj₁ adj₂ e
  let a := h.choose
  have hunit := h.choose_spec.1
  have huniq := h.choose_spec.2
  have ha (N : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
      (x : N.val.obj (op (n, U))) :
      (a.hom.app N).val.app (op (n, (proEtaleBaseChange f).obj U))
        (integralComparisonSequenceTensorSection l E L ι Z
          ((integralComparisonSequencePullback l E f).obj N)
          (op (n, (proEtaleBaseChange f).obj U)) 1
          (integralComparisonSequenceGenerator l E f N n U x)) =
        integralComparisonSequenceGenerator l L f
          ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N) n U
          (integralComparisonSequenceTensorSection l E L ι Y N (op (n, U)) 1 x) := by
    have hh := hunit N
    have hv := congrArg (fun q ↦ q.val.app (op (n, U)) x) hh
    dsimp only [Adjunction.comp_unit_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply] at hv
    change (e.inv.app _).val.app (op (n, U))
        ((pL.unit.app _).val.app (op (n, U))
          ((adjY.unit.app N).val.app (op (n, U)) x)) =
      (a.hom.app N).val.app (op (n, (proEtaleBaseChange f).obj U))
        ((adjZ.unit.app _).val.app (op (n, (proEtaleBaseChange f).obj U))
          ((pE.unit.app N).val.app (op (n, U)) x)) at hv
    rw [sequenceScalarPullbackRight_inv_app, hY, hZ] at hv
    exact hv.symm
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply huniq b
  intro N
  ext U x
  change (e.inv.app _).val.app U
      ((pL.unit.app _).val.app U ((adjY.unit.app N).val.app U x)) =
    (b.hom.app N).val.app ((integralComparisonSequenceBaseChange f).op.obj U)
      ((adjZ.unit.app _).val.app ((integralComparisonSequenceBaseChange f).op.obj U)
        ((pE.unit.app N).val.app U x))
  rw [sequenceScalarPullbackRight_inv_app, hY, hZ]
  exact (hb N U.unop.1 U.unop.2 x).symm


/-- The generator-normalized ordinary scalar comparison.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarPullback {Y Z : Scheme.{t}} (f : Z ⟶ Y) :=
  (integralComparisonSequenceScalarPullback_existsUnique l E L ι f).exists.choose

/-- The derived scalar comparison is the localization of that same entire-diagram
map; the equation uses the universal scalar counits, not only finite evaluations.
Source: Stacks 06YY, 0D6D
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: exact constant-coefficient inverse image preserves flat-term K-flat
complexes. Localize the ordinary tensor associator on K-flat resolutions using
the two universal scalar counits. Roofs give naturality and independence of
resolutions; their localization universal property gives uniqueness. -/
theorem integralComparisonSystemScalarPullback_existsUnique
    {Y Z : Scheme.{t}} (f : Z ⟶ Y) :
    ∃! a : integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequenceScalar l E L ι Z ≅
      integralComparisonDerivedSequenceScalar l E L ι Y ⋙
        integralComparisonDerivedSequencePullback l L f,
      ∀ (P : CochainComplex (coefficientSequenceModules l E Y) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients
          (R := coefficientSequenceCommRingSheaf l E Y) P →
        (integralComparisonDerivedSequenceScalar l E L ι Z).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app P) ≫
          (integralComparisonSequenceScalarModel l E L ι Z).ε.app
            (((integralComparisonSequencePullback l E f).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (integralComparisonSequenceScalarPullback l E L ι f) (.up ℤ)).hom.app P) =
        a.hom.app (DerivedCategory.Q.obj P) ≫
          (integralComparisonDerivedSequencePullback l L f).map
            ((integralComparisonSequenceScalarModel l E L ι Y).ε.app P) ≫
          (integralComparisonSequencePullback l L f).mapDerivedCategoryFactors.hom.app
            (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
              (.up ℤ)).obj P) := by
  let R := coefficientSequenceCommRingSheaf l E Y
  let S := coefficientSequenceCommRingSheaf l E Z
  let good : CochainComplex (coefficientSequenceModules l E Y) ℤ → Prop := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, max u (t + 1), max u (t + 1)}
        (R := R) (P.X i)
  have res : ∀ P, ∃ (Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (s : Q ⟶ P), good Q ∧ QuasiIso s := by
    intro P
    obtain ⟨Q, s, hQ, hf, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
    refine ⟨Q, s, ⟨hQ, ?_⟩, hs⟩
    intro i
    exact (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso R _).symm (hf i)
  have hflat : RepresentablyFlat (integralComparisonSequenceBaseChange f) := by
    have : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
    constructor
    intro A
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence A.1 A.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  have hS (P) (hP : good P) :
      IsIso ((integralComparisonSequenceScalarModel l E L ι Y).ε.app P) :=
    (integralComparisonSequenceScalarModel l E L ι Y).computes P hP.1
  have hT (P) (hP : good P) :
      IsIso ((integralComparisonSequenceScalarModel l E L ι Z).ε.app
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P)) := by
    apply (integralComparisonSequenceScalarModel l E L ι Z).computes
    exact SheafOfModules.continuousModulePullback_kFlat.{t + 1, t, t + 1, t, u}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology Z))
      (integralComparisonSequenceBaseChange f) R S
      (integralComparisonSequenceRingMap l E f)
      (integralComparisonSequencePullback l E f)
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)) P hP.1 hP.2
  obtain ⟨a, ha, hu⟩ := resolvingScalarSquare
    (integralComparisonSequencePullback l E f) (integralComparisonSequencePullback l L f)
    (integralComparisonSequenceScalarModel l E L ι Y).E
    (integralComparisonSequenceScalarModel l E L ι Z).E
    (integralComparisonSequenceScalarModel l E L ι Y).T
    (integralComparisonSequenceScalarModel l E L ι Z).T
    (integralComparisonSequenceScalarModel l E L ι Y).ε
    (integralComparisonSequenceScalarModel l E L ι Z).ε
    (integralComparisonSequenceScalarPullback l E L ι f) good res hS hT
  refine ⟨a, fun P _ ↦ ha P, ?_⟩
  intro b hb
  apply Iso.ext
  let ff := cochainRepresentativeWhiskering good res (coefficientSequenceDerived l L Z)
  apply ff.map_injective
  ext P
  have hx := hb P.obj P.property.1
  have hy := ha P.obj
  have hi := hS P.obj P.property
  have : IsIso ((integralComparisonSequencePullback l L f).mapDerivedCategory.map
      ((integralComparisonSequenceScalarModel l E L ι Y).ε.app P.obj) ≫
        (integralComparisonSequencePullback l L f).mapDerivedCategoryFactors.hom.app
          (((integralComparisonSequenceScalarModel l E L ι Y).E.mapHomologicalComplex
            (.up ℤ)).obj P.obj)) := by infer_instance
  exact (cancel_mono _).1 (hx.symm.trans hy)


/-- The localized entire-diagram scalar associator.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemScalarPullback {Y Z : Scheme.{t}} (f : Z ⟶ Y) :=
  (integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose




private theorem sequenceConstantId (Y : Scheme.{t})
    (A : CommRingCat.{max u (t + 1)}) :
    (Functor.sheafPushforwardContinuousNatTrans
      (F := proEtaleBaseChange (𝟙 Y)) (F' := 𝟭 Y.ProEt)
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom CommRingCat.{max u (t + 1)}
      (ProEt.topology Y) (ProEt.topology Y)).app
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A) =
      coefficientProEtaleDirectRingMap.{t, u} (𝟙 Y) A := by
  apply ((sheafificationAdjunction (ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  apply NatTrans.ext
  funext U
  change (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
    ((constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).obj A).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U.unop).op =
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{t, u} (𝟙 Y) A).hom.app U
  rw [sequenceConstantUnit]
  have hn := (toSheafify (ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U.unop).op
  change 𝟙 A ≫ _ = _ at hn
  rw [Category.id_comp] at hn
  exact hn.symm

private noncomputable def sequenceDirectId (Y : Scheme.{t}) :
    𝟭 (coefficientSequenceModules l E Y) ≅
      integralComparisonSequenceDirectImage l E (𝟙 Y) := by
  let e : integralComparisonSequenceBaseChange (𝟙 Y) ≅ 𝟭 _ :=
    NatIso.prod (Iso.refl _) (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y)
  exact (SheafOfModules.pushforwardId _).symm ≪≫
    SheafOfModules.pushforwardCongr₂ _ e (by
      ext U x
      let A := CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (U.unop.1 + 1)))
      change (coefficientSequenceCommRingPresheaf l E Y).map
        (Prod.mkHom (𝟙 U.unop.1)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U.unop.2)).op x =
        (coefficientProEtaleDirectRingMap (𝟙 Y) A).hom.app (op U.unop.2) x
      rw [sequenceRingVertical]
      exact congrArg (fun α ↦ α.hom.app (op U.unop.2) x) (sequenceConstantId Y A))


/-- The ordinary identity pullback is fixed by its adjunction-unit formula.
Source: Stacks 03D3, 0D6D
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: the pullback of the identity scheme map is naturally the identity by
the universal property of fibre products. The unit formula defines the mate
between the ordinary module inverse images. The adjunction bijection gives
uniqueness, and the inverse fibre-product map gives its inverse. -/
theorem integralComparisonSequenceUnit_existsUnique (Y : Scheme.{t}) :
    ∃! a : integralComparisonSequencePullback l E (𝟙 Y) ≅ 𝟭 _,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
        (x : M.val.obj (op (n, U))),
        (a.hom.app M).val.app (op (n, (proEtaleBaseChange (𝟙 Y)).obj U))
          (integralComparisonSequenceGenerator l E (𝟙 Y) M n U x) =
        M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)).op x := by
  let adj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (𝟙 Y))
  let d := sequenceDirectId l E Y
  let a := (conjugateIsoEquiv Adjunction.id adj).symm d
  have ha (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
      (x : M.val.obj (op (n, U))) :
      (a.hom.app M).val.app (op (n, (proEtaleBaseChange (𝟙 Y)).obj U))
        (integralComparisonSequenceGenerator l E (𝟙 Y) M n U x) =
      M.val.map (Prod.mkHom (𝟙 n)
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Y).hom.app U)).op x := by
    have hh := unit_conjugateEquiv_symm Adjunction.id adj d.hom M
    exact congrArg (fun q ↦ q.val.app (op (n, U)) x) hh.symm
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (adj.homEquiv M M).injective
  ext U x
  exact (hb M U.unop.1 U.unop.2 x).trans (ha M U.unop.1 U.unop.2 x).symm


/-- The specified identity inverse-image comparison on whole derived diagrams.
Source: Stacks 0D6D (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemUnit (Y : Scheme.{t}) :
    integralComparisonDerivedSequencePullback l E (𝟙 Y) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((integralComparisonSequenceUnit_existsUnique l E Y).exists.choose) ≪≫
      Functor.mapDerivedCategoryIdIso _

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

private theorem sequenceScalarMapComp (Y : Scheme.{t}) :
    integralComparisonSequenceScalarMap l E L ι Y ≫
      integralComparisonSequenceScalarMap l L M j Y =
        integralComparisonSequenceScalarMap l E M (j.comp ι) Y := by
  have hq (n : ℕ) : (integralScalarQuotientMap l L M j n).comp
      (integralScalarQuotientMap l E L ι n) =
        integralScalarQuotientMap l E M (j.comp ι) n := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  have hs (n : ℕ) : integralScalarQuotientSheafMap l E L ι Y n ≫
      integralScalarQuotientSheafMap l L M j Y n =
        integralScalarQuotientSheafMap l E M (j.comp ι) Y n := by
    unfold integralScalarQuotientSheafMap
    rw [← Functor.map_comp]
    congr 1
    ext x
    exact congrArg (fun f ↦ f x.down) (hq n)
  ext U : 3
  exact congrArg (fun α ↦ α.hom.app (op U.unop.2)) (hs U.unop.1)

/-- The ordinary scalar associator is fixed on sheafified tensor generators
on the whole sequence site. Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: send c tensor (b tensor x) to c*j(b) tensor x, with inverse c tensor x
to c tensor (1 tensor x). Balanced relations and sheafification extend these
formulas uniquely. The quotient maps are ring maps, so all horizontal squares
commute, and vertical restrictions commute by tensor functoriality. -/
theorem integralComparisonSequenceScalarComposition_existsUnique (Y : Scheme.{t}) :
    ∃! a : (integralComparisonSequenceScalarModel l E L ι Y).E ⋙
        (integralComparisonSequenceScalarModel l L M j Y).E ≅
      (integralComparisonSequenceScalarModel l E M (j.comp ι) Y).E,
      ∀ (N : coefficientSequenceModules l E Y) (U : (ℕ × Y.ProEt)ᵒᵖ)
        (c : (coefficientSequenceCommRingSheaf l M Y).obj.obj U)
        (b : (coefficientSequenceCommRingSheaf l L Y).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralComparisonSequenceTensorSection l L M j Y
            ((integralComparisonSequenceScalarModel l E L ι Y).E.obj N) U c
            (integralComparisonSequenceTensorSection l E L ι Y N U b x)) =
          integralComparisonSequenceTensorSection l E M (j.comp ι) Y N U
            (c * (integralComparisonSequenceScalarMap l L M j Y).hom.app U b) x := by
  let A := sequenceScalarPackage l E L ι Y
  let B := sequenceScalarPackage l L M j Y
  let D := sequenceScalarPackage l E M (j.comp ι) Y
  have hφ := (sequenceScalarMapComp l E L ι M j Y).symm
  let a := SheafOfModules.systemScalarModelComposition hφ A B D
  have ha := SheafOfModules.systemScalarModelComposition_tmul hφ A B D
  refine ⟨a, ?_, ?_⟩
  · intro N U c b x
    simp only [sequenceTensorSection_eq]
    exact ha N U c b x
  · intro b hb
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (B.ordinaryAdj.homEquiv _ _).injective
    apply SheafOfModules.systemScalarModel_hom_ext A N _
    intro V y
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change (b.hom.app N).val.app V
        ((B.ordinaryAdj.unit.app (A.model.E.obj N)).val.app V
          (SheafOfModules.systemModelTmul A.model N V 1 y)) =
      (a.hom.app N).val.app V
        ((B.ordinaryAdj.unit.app (A.model.E.obj N)).val.app V
          (SheafOfModules.systemModelTmul A.model N V 1 y))
    rw [B.unit_normalized]
    have hh := hb N V 1 1 y
    simp only [sequenceTensorSection_eq] at hh
    exact hh.trans (ha N V 1 1 y).symm


/-- The strict scalar associator used before realization.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarComposition (Y : Scheme.{t}) :=
  (integralComparisonSequenceScalarComposition_existsUnique l E L ι M j Y).exists.choose

end WeilConjectures

namespace WeilConjectures
open scoped ChangeOfRings

/-- The chosen ordinary identity inverse-image map, prior to localization.
Source: Stacks 0D6D, 03D3 (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :=
  (integralComparisonSequenceUnit_existsUnique l E X).exists.choose

private theorem sequenceScalarMapId (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :
    integralComparisonSequenceScalarMap l E E (AlgHom.id ℚ_[l] E) X = 𝟙 _ := by
  have hq (n : ℕ) : integralScalarQuotientMap l E E (AlgHom.id ℚ_[l] E) n =
      RingHom.id _ := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  have hs (n : ℕ) : integralScalarQuotientSheafMap l E E (AlgHom.id ℚ_[l] E) X n =
      𝟙 _ := by
    unfold integralScalarQuotientSheafMap
    rw [hq]
    have hid : CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((RingHom.id _).comp (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)) =
        𝟙 (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))) := by
      ext x
      rfl
    rw [hid]
    exact (constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map_id _
  ext U : 3
  exact congrArg (fun α ↦ α.hom.app (op U.unop.2)) (hs U.unop.1)

/-- Multiplication determines the identity scalar extension on whole quotient systems.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems).
Proof: multiplication of a scalar and a module section is balanced and commutes with
all quotient transitions and restrictions. Sheafification extends it to scalar change.
The inverse inserts the scalar one. The tensor relations give both inverse equations,
and local generation by tensors gives uniqueness. -/
theorem integralComparisonSequenceScalarUnit_existsUnique (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :
    ∃! a : (integralComparisonSequenceScalarModel l E E (AlgHom.id ℚ_[l] E) X).E ≅ 𝟭 _,
      ∀ (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l E X).obj.obj U) (x : N.val.obj U),
        (a.hom.app N).val.app U
          (integralComparisonSequenceTensorSection l E E (AlgHom.id ℚ_[l] E) X N U s x) =
            s • x := by
  let A := sequenceScalarPackage l E E (AlgHom.id ℚ_[l] E) X
  have hφ := sequenceScalarMapId l E X
  let a := SheafOfModules.systemScalarModelUnit hφ A
  have ha (N : coefficientSequenceModules l E X) (U : (ℕ × X.ProEt)ᵒᵖ)
      (s : (coefficientSequenceCommRingSheaf l E X).obj.obj U) (x : N.val.obj U) :
      (a.hom.app N).val.app U (SheafOfModules.systemModelTmul A.model N U s x) =
        s • x := SheafOfModules.systemScalarModelUnit_tmul hφ A N U s x
  refine ⟨a, ?_, ?_⟩
  · intro N U s x
    rw [sequenceTensorSection_eq]
    exact ha N U s x
  · intro b hb
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply SheafOfModules.systemScalarModel_hom_ext A N N
    intro U x
    rw [← sequenceTensorSection_eq]
    exact (hb N U 1 x).trans (by rw [sequenceTensorSection_eq]; exact (ha N U 1 x).symm)


/-- Multiplication on the actual quotient systems is the scalar unit.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :=
  (integralComparisonSequenceScalarUnit_existsUnique l E X).exists.choose

end WeilConjectures
