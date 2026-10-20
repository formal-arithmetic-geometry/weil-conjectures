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

/-- Exactness of constant-coefficient system inverse image. Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems).
Proof: evaluate at each positive exponent. The unit-normalized inverse-image
adjunction is the finite constant-coefficient adjunction, which is exact.
Kernels, cokernels and addition in the system category are levelwise. -/
theorem integralComparisonSequencePullback_exact {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (integralComparisonSequencePullback l E f).Additive ∧
      PreservesFiniteLimits (integralComparisonSequencePullback l E f) ∧
      PreservesFiniteColimits (integralComparisonSequencePullback l E f) := by
  sorry

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

/-- Derived scalar extension of whole strict coefficient systems, retaining homotopies.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonDerivedSequenceScalar (X : Scheme.{t}) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l L X :=
  (integralComparisonSequenceScalarModel l E L ι X).T

/-- The system pullback generator is the actual adjunction unit on sections.
Source: Stacks 03D2, 0941
(blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceGenerator {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt)
    (x : M.val.obj (op (n, U))) :=
  (((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).unit.app M).val.app (op (n, U))) x

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
  sorry

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
  sorry

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
  sorry

/-- The localized entire-diagram scalar associator.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemScalarPullback {Y Z : Scheme.{t}} (f : Z ⟶ Y) :=
  (integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose




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
  sorry

/-- The specified identity inverse-image comparison on whole derived diagrams.
Source: Stacks 0D6D (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSystemUnit (Y : Scheme.{t}) :
    integralComparisonDerivedSequencePullback l E (𝟙 Y) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((integralComparisonSequenceUnit_existsUnique l E Y).exists.choose) ≪≫
      Functor.mapDerivedCategoryIdIso _

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (j : L →ₐ[ℚ_[l]] M)

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
  sorry

/-- The strict scalar associator used before realization.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarComposition (Y : Scheme.{t}) :=
  (integralComparisonSequenceScalarComposition_existsUnique l E L ι M j Y).exists.choose

end WeilConjectures

namespace WeilConjectures

/-- The chosen ordinary identity inverse-image map, prior to localization.
Source: Stacks 0D6D, 03D3 (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :=
  (integralComparisonSequenceUnit_existsUnique l E X).exists.choose

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
  sorry

/-- Multiplication on the actual quotient systems is the scalar unit.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-sequence-systems). -/
def integralComparisonSequenceScalarUnit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{t}) :=
  (integralComparisonSequenceScalarUnit_existsUnique l E X).exists.choose

end WeilConjectures
