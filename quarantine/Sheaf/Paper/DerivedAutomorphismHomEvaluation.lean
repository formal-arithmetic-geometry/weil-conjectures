/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage

import Sheaf.Paper.PurInverseImageTensorHom
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses

/-! # Internal Hom and evaluation under coefficient-site isomorphisms

Source: Stacks Project, Modules on Sites, Tag 0GMX; the derived and completed
normalization is the enhancement in the node's sixteen proof steps, supplying
main-20261015 prop-pod-dual-tate-data-compatibility Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Finite inputs are unbounded. Integral inputs have exactly the recorded
Hom-constructibility condition. Completed inverse image is constructed from
all coefficient projections; its comparison with tower pullback uses the
actual completion unit and a resolution-normalized total-limit comparison.
System maps and their identities are stated before evaluation or realization.
Rational maps are localized; algebraically closed maps use every common stage.

## Main definitions

* `podFiniteHomComparison`: transpose of pullback of finite evaluation.
* `podPartialHomComparison`: the same construction on permitted Hom pairs.
* `podCompletedRingMap`: completed coefficient transport from all projections.
* `podCompletedToTower`: the completion-unit comparison with tower pullback.

## Main statements

* `derivedAutomorphismHomEvaluation`: the four evaluation-defined natural isomorphisms.
* The `*_laws`, `*_shift`, `*_comp` declarations give all coherent identities.
* `podHomReductionSquare`: the actual system-level reduction square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v a b c d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Partial closed data on precisely the pairs for which internal Hom is permitted.
Source: Stacks 08J9 and the integral qualification in the node
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
structure PodPartialClosed {C : Type a} [Category.{b} C] [Preadditive C]
    (T : C × C ⥤ C) (J : ObjectProperty (Cᵒᵖ × C)) (H : J.FullSubcategory ⥤ C) where
  /-- Tensor-Hom transposition on every permitted pair. -/
  transpose : ∀ (L : C) (P : J.FullSubcategory),
    (T.obj (L, P.obj.1.unop) ⟶ P.obj.2) ≃+ (L ⟶ H.obj P)
  /-- Naturality in the tensor parameter. -/
  parameter_naturality : ∀ (L L' : C) (P : J.FullSubcategory) (f : L' ⟶ L)
    (h : T.obj (L, P.obj.1.unop) ⟶ P.obj.2),
    transpose L' P (T.map (Prod.mkHom f (𝟙 _)) ≫ h) = f ≫ transpose L P h

/-- Evaluation is the inverse transpose of the identity, with Hom first.
The node's argument-first convention is obtained by the canonical Koszul symmetry.
Source: Stacks 08J9 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodPartialClosed.evaluation {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (P : J.FullSubcategory) :
    T.obj (H.obj P, P.obj.1.unop) ⟶ P.obj.2 :=
  (S.transpose _ P).symm (𝟙 _)

/-- The genuine functor on permitted Hom pairs induced by pullback.
Source: Stacks 0GMX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podPairPullback {C : Type a} {D : Type c} [Category.{b} C] [Category.{d} D]
    (F : C ⥤ D) (J : ObjectProperty (Cᵒᵖ × C)) (K : ObjectProperty (Dᵒᵖ × D))
    (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj)) :
    J.FullSubcategory ⥤ K.FullSubcategory :=
  K.lift (J.ι ⋙ F.op.prod F) h

/-- The evaluation-defined comparison, using the specified tensor comparison.
Its data are a closed transpose, never an arbitrary chosen isomorphism.
Source: Stacks 0GMX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podPartialHomComparison {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (P : J.FullSubcategory) :
    F.obj (HC.obj P) ⟶ HD.obj ((podPairPullback F J K h).obj P) :=
  SD.transpose _ _ ((μ (HC.obj P) P.obj.1.unop).inv ≫ F.map (SC.evaluation P))

/-- The displayed naturality, evaluation, and transposition identities, together
with invertibility of the evaluation-defined map. All arrows are in the stated
category itself, including when that category is a derived system category.
Source: Stacks 0GMX, node proof steps 3--5
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
structure PodPartialHomCompatibility {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M)) : Prop where
  /-- The canonical comparison is invertible on exactly the permitted pairs. -/
  isIso : ∀ P, IsIso (podPartialHomComparison SC SD F h μ P)
  /-- Naturality includes arbitrary arrows of the actual input category. -/
  naturality : ∀ (P Q : J.FullSubcategory) (f : P ⟶ Q),
    F.map (HC.map f) ≫ podPartialHomComparison SC SD F h μ Q =
      podPartialHomComparison SC SD F h μ P ≫ HD.map ((podPairPullback F J K h).map f)
  /-- The evaluation square, written with Hom first in the tensor. -/
  evaluation : ∀ P : J.FullSubcategory,
    (μ (HC.obj P) P.obj.1.unop).hom ≫
      TD.map (Prod.mkHom (podPartialHomComparison SC SD F h μ P) (𝟙 _)) ≫
        SD.evaluation ((podPairPullback F J K h).obj P) = F.map (SC.evaluation P)
  /-- Preservation of every transpose, with the inverse tensor comparison. -/
  transpose : ∀ (L : C) (P : J.FullSubcategory)
    (f : TC.obj (L, P.obj.1.unop) ⟶ P.obj.2),
    SD.transpose _ _ ((μ L P.obj.1.unop).inv ≫ F.map f) =
      F.map (SC.transpose L P f) ≫ podPartialHomComparison SC SD F h μ P

section Finite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The finite unbounded comparison: transpose of pullback of ordinary evaluation.
Source: Stacks 0GMX, node proof steps 3--5
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteHomComparison (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finiteDerivedPullback l E n g).obj
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) ⟶
      (finiteIntrinsicDerivedInternalHom l E X n).obj
        (op ((finiteDerivedPullback l E n g).obj M),
          (finiteDerivedPullback l E n g).obj N) :=
  (finiteIntrinsicTranspose l E X n) _ _ _
    ((canonicalFinitePullbackTensor l E g n
      ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) M).inv ≫
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E Y n M N))

/-- Finite unbounded internal Hom is preserved, naturally and with its actual evaluation
and transposition. Source: Stacks 0GMX, node proof steps 1--5.
Proof: reindex by the isomorphism of sites. It is exact and preserves K-injectives,
K-flat complexes, products and total tensor. Reindex each Hom-product factor;
the signed differential commutes. Localize this isomorphism. On pure tensors
both evaluation composites evaluate the same local homomorphism. Currying gives
the transposition equation; uncurrying gives naturality in both arguments.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteHomComparison_laws (n : ℕ) :
    (∀ M N, IsIso (podFiniteHomComparison l E g n M N)) ∧
    (∀ M N M' N' (a : M' ⟶ M) (b : N ⟶ N'),
      (finiteDerivedPullback l E n g).map
          ((finiteIntrinsicDerivedInternalHom l E Y n).map (Prod.mkHom a.op b)) ≫
        podFiniteHomComparison l E g n M' N' =
      podFiniteHomComparison l E g n M N ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map
          (Prod.mkHom ((finiteDerivedPullback l E n g).map a).op
            ((finiteDerivedPullback l E n g).map b))) ∧
    (∀ M N,
      (canonicalFinitePullbackTensor l E g n
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) M).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (podFiniteHomComparison l E g n M N) (𝟙 _)) ≫
        finiteIntrinsicEvaluation l E X n
          ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
      (finiteDerivedPullback l E n g).map (finiteIntrinsicEvaluation l E Y n M N)) ∧
    (∀ L M N (b : (finiteIntrinsicDerivedTensor l E Y n).obj (L, M) ⟶ N),
      finiteIntrinsicTranspose l E X n _ _ _
        ((canonicalFinitePullbackTensor l E g n L M).inv ≫
          (finiteDerivedPullback l E n g).map b) =
      (finiteDerivedPullback l E n g).map (finiteIntrinsicTranspose l E Y n L M N b) ≫
        podFiniteHomComparison l E g n M N) := by
  sorry
end Finite


section IntegralClosed
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The actual ordinary-to-completed tensor unit: reduction's adjunction unit,
its tensor comparison, and the inverse of the recorded Roos realization.
Source: node proof step 10, Stacks 099B
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedTensorUnit (M N : DerivedCategory (integralTowerModules l E W)) :
    (pullbackTensorCalculus l E W).integralClosed.tensor.obj (M, N) ⟶
      (integralCompletedTensor l E W).obj (M, N) :=
  (pullbackTensorCalculus l E W).adjunction.unit.app _ ≫
    (coefficientSequenceLimit l E W).map
      ((pullbackTensorCalculus l E W).reductionTensor.hom.app (M, N)) ≫
    (pullbackTensorIntegralTensorModel l E W).inv.app (M, N)

/-- The completed closed adjunction is uniquely normalized by ordinary evaluation
precomposed with the actual completion unit. No perfectness assumption is imposed.
Source: node proof steps 10--11, Stacks 099B, 0A0E.
Proof: the constant/completed coefficient equivalence identifies quotient-tower
completion with the Koszul reflector, preserving the unit. Maps from the completed
tensor into the complete target N are therefore exactly maps from the ordinary
tensor. Compose this bijection with ordinary tensor-Hom transposition. The Hom
object is constructible by the pair condition, so full-subcategory Hom is unchanged.
Both bijections are additive and natural. The equation fixes every transpose,
hence fixes the partial closed data uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralClosed_existsUnique :
    ∃! S : PodPartialClosed (constructibleIntegralTensor l E W)
        (constructibleIntegralHomPairs l E W) (constructibleIntegralHom l E W),
      ∀ (L : sfIntegralConstructibleCategory l E W)
        (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
        (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2),
        HEq ((S.transpose L P f).hom)
          ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
            P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom)) := by
  sorry

/-- Completed transposition with its unique ordinary-unit normalization.
Source: Stacks 099B (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralClosed := (podIntegralClosed_existsUnique l E W).exists.choose
end IntegralClosed

section IntegralTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The Hom-constructible domain is preserved by isomorphism pullback.
Source: node proof steps 3, 8, 11.
Proof: exact sectionwise reindexing preserves K-injectives, hence the ambient
Hom complex. Its canonical completion-unit comparison identifies reindexing
with the recorded tower pullback on complete inputs. The source Hom is
constructible by hypothesis, and pullback preserves constructibility.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPairs_pullback
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    constructibleIntegralHomPairs l E X
      (((constructibleIntegralPullback l E g).op.prod
        (constructibleIntegralPullback l E g)).obj P.obj) := by
  sorry

/-- The integral comparison is the transpose of completed pullback of evaluation.
Source: node proof steps 10--11, Stacks 0GMX
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralHomComparison :=
  podPartialHomComparison (podIntegralClosed l E Y) (podIntegralClosed l E X)
    (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g)

/-- Integral invertibility, naturality, evaluation and every transpose, using
completed tensor and exactly the stated Hom-constructible domain.
Source: node proof steps 8--11.
Proof: reindex the completed-ring Hom complex. The canonical unit and the two
Roos-coordinate comparisons identify this map with tower-defined pullback.
Precompose evaluation with the ordinary-to-completed tensor unit; the equation
is the ordinary Hom-complex evaluation equation. The reflector's Hom bijection
then gives the completed equation. Currying proves transposition and naturality.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomComparison_laws :
    PodPartialHomCompatibility (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
        (canonicalIntegralPullbackTensor l E g) := by
  sorry
end IntegralTransport

section RationalClosed
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The rational transpose is the unique additive localization of the integral
transpose. The equation fixes inverse transposition on every pure tensor in the
actual localized Hom groups, including its scalar.
Source: node proof step 14.
Proof: integral transposition is O_E-linear, so tensor it with E. Its inverse
localizes too. The unchanged integral objects and the prescribed rational
operation formulas identify the endpoints. Pure tensors generate each Hom
module, so the normalization determines both maps uniquely; balancing and
naturality descend from their integral versions.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalClosed_existsUnique :
    ∃! S : PodPartialClosed (rationalDerivedTensor l E W)
        (constructibleRationalHomPairs l E W) (rationalDerivedInternalHom l E W),
      ∀ (L : sfRationalConstructibleCategory l E W)
        (P : (constructibleRationalHomPairs l E W).FullSubcategory)
        (f : L.obj ⟶ (constructibleIntegralHom l E W).obj
          (integralPairOfRationalHomPair l E W P))
        (a : Localization.Away (Padic.coefficientExtensionUniformizer l E))
        (q : L ⟶ (rationalDerivedInternalHom l E W).obj P),
        HEq q (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] f) →
        HEq ((S.transpose L P).symm q)
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
            ((podIntegralClosed l E W).transpose L.obj
              (integralPairOfRationalHomPair l E W P)).symm f) := by
  sorry

/-- The uniquely localized completed closed data.
Source: node proof step 14 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podRationalClosed := (podRationalClosed_existsUnique l E W).exists.choose
end RationalClosed

section RationalTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Rational pullback preserves the same integral Hom-pair condition.
Source: node proof step 14.
Proof: the rational operations keep integral objects. Their object formulas
identify this condition with podIntegralPairs_pullback.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalPairs_pullback
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    constructibleRationalHomPairs l E X
      (((rationalDerivedPullback l E g).op.prod (rationalDerivedPullback l E g)).obj P.obj) := by
  sorry

/-- The rational comparison uses precisely localized tensor and evaluation.
Source: node proof step 14 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podRationalHomComparison :=
  podPartialHomComparison (podRationalClosed l E Y) (podRationalClosed l E X)
    (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g)

/-- Rational maps are the localized integral maps, and naturality holds for
arbitrary localized Hom arrows, including sums of pure tensors.
Source: node proof step 14.
Proof: localize the integral comparison and its inverse. On pure tensors the
closed normalization gives the displayed map; additivity and balancing extend
this to all arrows. Expand each naturality and evaluation equation bilinearly
and apply the integral equation to each summand. Transposition is linear too.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalHomComparison_laws :
    PodPartialHomCompatibility (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
        (canonicalRationalPullbackTensor l E g) ∧
    ∀ P : (constructibleRationalHomPairs l E Y).FullSubcategory,
      HEq (podRationalHomComparison l E g P)
        ((sfRationalConstructibleLocalization l E X).map
          (podIntegralHomComparison l E g (integralPairOfRationalHomPair l E Y P))) := by
  sorry
end RationalTransport


section CommonClosed
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

set_option backward.isDefEq.respectTransparency true in
/-- Exact common-stage normalization of inverse transposition, at every finite
stage containing the entries. The implications only reconcile the recorded
operation objects with their literal pair representatives, whose equality is
part of the owning operation definitions; they impose no condition on arrows.
Source: node proof steps 15--16
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodCommonTransposeNormalization
    (S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W)) : Prop :=
  ∀ (L : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (hL : L.stage ≤ F) (hP : (commonStageHomObject l Ω W P).stage ≤ F)
    (hT : (commonStageTensorObject l Ω W L P.obj.1.unop).stage ≤ F)
    (hN : P.obj.2.stage ≤ F)
    (φ : L.toStage hL ⟶ (commonStageHomObject l Ω W P).toStage hP)
    (q : L ⟶ (commonStageDerivedInternalHom l Ω W).obj P),
    HEq q (ofHom L (commonStageHomObject l Ω W P) F hL hP φ) →
    HEq ((S.transpose L P).symm q)
      (ofHom (commonStageTensorObject l Ω W L P.obj.1.unop) P.obj.2 F hT hN
        ((commonStageTensorComparison l Ω W L P.obj.1.unop F hT).hom ≫
          ((podRationalClosed l (Coefficient.{u} l Ω F) W).transpose (L.toStage hL)
            (commonStageHomPairAtStage l Ω W P F hP)).symm
              (φ ≫ (commonStageHomComparison l Ω W P F hP).hom)))

/-- Common-stage closed maps are determined by rational transposition at every
larger finite field, and are natural on the actual Hom-colimit category.
Source: node proof steps 15--16.
Proof: put the parameter, pair and arrow over a common finite field. Apply the
rational inverse transpose, conjugating by the recorded tensor and Hom stage
comparisons. Finite free coefficient extension preserves the evaluation formula,
without requiring the first input to be perfect: Hom commutes with the finite
direct sum of its coefficient copies. Transposition therefore commutes with
further scalar extension. This proves independence of enlargement and eventual
equality. The rational inverse maps prove bijectivity; addition and naturality
can be checked at one common stage. Every arrow has such a representative, so
the normalization determines the closed data uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonClosed_existsUnique :
    ∃! S : PodPartialClosed (commonStageDerivedTensor l Ω W)
      (commonStageHomPairs l Ω W) (commonStageDerivedInternalHom l Ω W),
      PodCommonTransposeNormalization l Ω W S := by
  sorry

/-- The closed data normalized on all common finite-field representatives.
Source: node proof step 16 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCommonClosed := (podCommonClosed_existsUnique l Ω W).exists.choose
end CommonClosed

section CommonTransport
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Isomorphism pullback preserves the permitted common-stage Hom pairs.
Source: node proof steps 15--16.
Proof: at the finite compositum use podRationalPairs_pullback, then the
prescribed pullback/scalar comparison to identify both entries. Hom of the
resulting pair is isomorphic to the pulled back Hom, so is constructible.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonPairs_pullback
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    commonStageHomPairs l Ω X
      (((commonStageDerivedPullback l Ω g).op.prod
        (commonStageDerivedPullback l Ω g)).obj P.obj) := by
  sorry

/-- The common-stage comparison is the transpose of the prescribed common-stage
tensor/evaluation composite on the actual pair category.
Source: node proof step 16 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCommonHomComparison :=
  podPartialHomComparison (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
    (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g)

/-- Invertibility and all displayed identities on the algebraically closed
coefficient category, naturally for arbitrary common-stage morphisms.
Source: node proof steps 15--16.
Proof: put every arrow in a proposed equation over one common finite field.
The normalized transpose and tensor comparison identify the comparison there
with the rational evaluation-defined comparison. Its inverse, naturality,
evaluation and transposition equations hold by podRationalHomComparison_laws.
Finite free scalar compatibility makes their classes independent of the
chosen stage and arrow representative, including eventual equality.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_laws :
    PodPartialHomCompatibility (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
        (canonicalCommonStagePullbackTensor l Ω g) := by
  sorry
end CommonTransport

section Systems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The comparison is an actual map on the unbounded derived category of strict
systems, defined before finite evaluation or total-limit realization.
Source: node proof steps 12--13, Stacks 0941 and 0GMX
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podSystemHomComparison :=
  coefficientBaseChangeHom (pullbackTensorCalculus l E Y).systemClosed
    (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
      (pullbackTensorSystemComparison l E g)

/-- System reindexing preserves internal Hom and the actual system evaluation,
transposes and internal composition, without inferring equality from evaluations.
Source: node proof step 12.
Proof: reindex the sequence site while fixing its index. This is an exact
module equivalence, with inverse reindexing; it preserves K-injectives and
K-flats by transporting null homotopies and acyclic tensor tests. The Hom
product comparison and tensor comparison commute with the signed differential.
Evaluation is the same chain map before localization. Currying gives every
transpose and composition equation on the derived system category itself.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_laws :
    (∀ M N, IsIso (podSystemHomComparison l E g M N)) ∧
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
        (pullbackTensorSystemComparison l E g) := by
  sorry
end Systems


section CompletedReindexing
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Pullback of the nth completed-ring projection, followed by the uniquely
constant-section-normalized finite coefficient map.
Source: node proof step 1 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedRingProjection (n : ℕᵒᵖ) :
    (isoSectionwiseInverseImage g RingCat.{u+1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (integralCoefficientSheafSystem l E X).obj n :=
  (isoSectionwiseInverseImage g RingCat.{u+1}).map
      (limit.π (integralCoefficientSheafSystem l E Y) n) ≫
    isoSectionwiseConstantMap.{u, u} g
      (CommRingCat.of (ULift.{u+1} (finiteCoefficientRing l E (n.unop + 1))))

/-- The projection maps respect every coefficient quotient arrow.
Source: node proof step 1, Stacks 0H7J.
Proof: the limit projections respect every quotient. Constant-section maps
commute with quotient homomorphisms by the sheafification universal property.
Compose these two naturality equations.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedRingProjection_naturality {m n : ℕᵒᵖ} (f : m ⟶ n) :
    podCompletedRingProjection l E g m ≫ (integralCoefficientSheafSystem l E X).map f =
      podCompletedRingProjection l E g n := by
  sorry

/-- The actual completed coefficient transport, constructed by the limit lift
of all finite projections. Source: node proof step 1, Stacks 0038
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedRingMap :
    (isoSectionwiseInverseImage g RingCat.{u+1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X :=
  limit.lift (integralCoefficientSheafSystem l E X)
    { pt := _
      π := { app := podCompletedRingProjection l E g
             naturality := fun _ _ f ↦
               (Category.id_comp _).trans (podCompletedRingProjection_naturality l E g f).symm } }

/-- Completed-ring transport is invertible with precisely the prescribed
projections. Source: node proof step 1, Stacks 0038.
Proof: the site equivalence preserves the inverse limit. Each finite coefficient
comparison is invertible. The induced map of limit cones is therefore invertible.
Its composites with the projections are the defining limit-lift equations.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedRingMap_isIso : IsIso (podCompletedRingMap l E g) := by
  sorry

/-- Use the proved invertibility of the actual limit-lift map.
Source: Stacks 0038 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedRingMapIsIso : IsIso (podCompletedRingMap l E g) :=
  podCompletedRingMap_isIso l E g

/-- Exact inverse image on modules over the completed ring sheaf, sectionwise
with the transported coefficient action. Source: node proof step 1
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedModuleInverseImage : integralTowerModules l E Y ⥤ integralTowerModules l E X :=
  isoSectionwiseModuleInverseImage.{u, u} g (podCompletedRingMap l E g)

/-- Additivity inherited from the published exact sectionwise inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleAdditive : (podCompletedModuleInverseImage l E g).Additive :=
  isoSectionwiseModuleInverseImage_additive.{u, u} g (podCompletedRingMap l E g)

/-- Left exactness inherited from the published inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleLimits : PreservesFiniteLimits (podCompletedModuleInverseImage l E g) :=
  isoSectionwiseModuleInverseImage_limits.{u, u} g (podCompletedRingMap l E g)

/-- Right exactness inherited from the published inverse image.
Source: Stacks 03DA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedModuleColimits :
    PreservesFiniteColimits (podCompletedModuleInverseImage l E g) :=
  isoSectionwiseModuleInverseImage_colimits.{u, u} g (podCompletedRingMap l E g)

/-- The unbounded derived exact inverse-image equivalence, with the standard
termwise localization and its standard shift comparison.
Source: node proof steps 1--2 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedDerivedInverseImage := (podCompletedModuleInverseImage l E g).mapDerivedCategory

/-- The standard exact-derived shift structure on the sectionwise functor.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
instance podCompletedDerivedCommShift :
    (podCompletedDerivedInverseImage l E g).CommShift ℤ :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleColimits l E g
  inferInstanceAs ((podCompletedModuleInverseImage l E g).mapDerivedCategory.CommShift ℤ)

/-- Sectionwise completed inverse image is an equivalence.
Source: node proof steps 1--2.
Proof: reindex with the inverse scheme isomorphism and inverse coefficient map.
Both composites are identity on every coefficient projection, hence on the
completed ring and its actions. The identity-on-sections maps give the natural
unit and counit. Deriving preserves their inverse identities.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedInverseImage_equivalence :
    (podCompletedModuleInverseImage l E g).IsEquivalence ∧
      (podCompletedDerivedInverseImage l E g).IsEquivalence := by
  sorry

/-- Restriction and reindexing agree by the inverse-image unit on every local
section. This specifies the ordinary comparison before passing to derived maps.
Source: node proof steps 1 and 8.
Proof: after scalar restriction the underlying sheaf of a finite module is
unchanged. The canonical isomorphism from intrinsic inverse image to sectionwise
reindexing sends its adjunction-unit section to restriction along the counit
of postcomposition/base-change. The completed ring map commutes with the finite
projection, so the same section map is linear for the completed action.
The unit determines the comparison uniquely; inverse site reindexing gives
its inverse, and local generation by unit sections proves naturality.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteRestrictionOrdinary_existsUnique (n : ℕ) :
    ∃! e : sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g ⋙
        scalarReductionRestriction l E X n ≅
      scalarReductionRestriction l E Y n ⋙ podCompletedModuleInverseImage l E g,
      ∀ (M : normalizedDVRModules l E Y n) (V : Y.ProEt)
        (x : M.val.obj (op V)),
        HEq (((e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V)))
          ((((sfIntrinsicConstantModuleAdjunction g
            (finiteCoefficientRing l E (n + 1))).unit.app M).val.app (op V)) x))
          ((M.val.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
            (inferInstance : WeaklyEtale g) trivial).counit.app V).op) x) := by
  sorry

/-- The uniquely section-normalized ordinary coefficient restriction comparison.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteRestrictionOrdinary (n : ℕ) :=
  (podFiniteRestrictionOrdinary_existsUnique l E g n).exists.choose

/-- Derived finite restriction/reindexing comparison induced from that same
ordinary section map. Source: node proof step 8
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteRestriction (n : ℕ) :
    finiteDerivedPullback l E n g ⋙ coefficientFiniteDerivedRestriction l E X n ≅
      coefficientFiniteDerivedRestriction l E Y n ⋙ podCompletedDerivedInverseImage l E g :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleColimits l E g
  (Functor.mapDerivedCategoryCompIso
    (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g)
    (scalarReductionRestriction l E X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (podFiniteRestrictionOrdinary l E g n) ≪≫
      Functor.mapDerivedCategoryCompIso (scalarReductionRestriction l E Y n)
        (podCompletedModuleInverseImage l E g)


/-- The actual ordinary limit projection, with the restriction/evaluation identity.
Source: Stacks 0941 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podOrdinaryProjection (W : Scheme.{u}) (n : ℕ) :
    pullbackTensorOrdinaryLimit l E W ⟶
      coefficientSequenceEvaluation l E W n ⋙ scalarReductionRestriction l E W n :=
  Functor.whiskerLeft (coefficientSequenceRestriction l E W) (lim.π (op n)) ≫
    eqToHom (coefficientSequenceRestriction_evaluation l E W n)

/-- The unit-normalized ordinary system/finite pullback comparison.
Source: node proof step 12 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podSystemEvaluationOrdinary (n : ℕ) :
    pullbackTensorSequenceInverse l E g ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) g :=
  (pullbackTensorSequenceInverseEvaluation l E g n).symm ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E Y n)
      (pullbackTensorLevelIntrinsic l E g n)

/-- Ordinary limits commute with the exact equivalence, uniquely on all projections.
Source: node proof step 8, Stacks 0038.
Proof: the two functors take the ordinary limit of the same reindexed diagram.
The finite restriction comparisons identify their cones. The limit universal
property supplies the comparison and its inverse, and jointly monic ordinary
projections prove naturality and uniqueness.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podOrdinaryLimitReindexing_existsUnique :
    ∃! e : pullbackTensorSequenceInverse l E g ⋙ pullbackTensorOrdinaryLimit l E X ≅
        pullbackTensorOrdinaryLimit l E Y ⋙ podCompletedModuleInverseImage l E g,
      ∀ (N : coefficientSequenceModules l E Y) (n : ℕ),
        e.hom.app N ≫ (podCompletedModuleInverseImage l E g).map
          ((podOrdinaryProjection l E Y n).app N) =
        (podOrdinaryProjection l E X n).app ((pullbackTensorSequenceInverse l E g).obj N) ≫
        (scalarReductionRestriction l E X n).map
          ((podSystemEvaluationOrdinary l E g n).hom.app N) ≫
        (podFiniteRestrictionOrdinary l E g n).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj N) := by
  sorry

/-- The ordinary projection-normalized limit comparison.
Source: Stacks 0038 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podOrdinaryLimitReindexing :=
  (podOrdinaryLimitReindexing_existsUnique l E g).exists.choose

/-- Resolution normalization for total derived-limit reindexing, imposed before
any finite evaluation. This is the right-derived universal-property square.
Source: node proof steps 8 and 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodLimitResolutionNormalization
    (e : pullbackTensorSequenceDerived l E g ⋙ coefficientSequenceLimit l E X ≅
      coefficientSequenceLimit l E Y ⋙ podCompletedDerivedInverseImage l E g) : Prop :=
  ∀ C : CochainComplex (coefficientSequenceModules l E Y) ℤ,
    pullbackTensorLimitUnit l E X
        (((pullbackTensorSequenceInverse l E g).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (coefficientSequenceLimit l E X).map
        ((pullbackTensorSequenceInverse l E g).mapDerivedCategoryFactors.inv.app C) ≫
      e.hom.app (DerivedCategory.Q.obj C) =
    DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (podOrdinaryLimitReindexing l E g) (.up ℤ)).hom.app C) ≫
      (podCompletedModuleInverseImage l E g).mapDerivedCategoryFactors.inv.app
        (((pullbackTensorOrdinaryLimit l E Y).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (podCompletedDerivedInverseImage l E g).map (pullbackTensorLimitUnit l E Y C)

/-- Exact reindexing commutes with functorial total derived limit, fixed on
resolutions and commuting with every actual finite reduction projection.
Source: node proof steps 8 and 13.
Proof: exact inverse reindexing transports null homotopies, hence K-injective
resolutions in the ordinary system category. Derive the single ordinary limit
comparison using those resolutions. The total derived-functor universal property
fixes the transformation by the displayed unit square, hence uniquely. The
ordinary projection equations give its derived projection equations. Inverse
reindexing gives its inverse. No equality of maps is inferred from finite
projections in a derived category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podLimitReindexing_existsUnique :
    ∃! e : pullbackTensorSequenceDerived l E g ⋙ coefficientSequenceLimit l E X ≅
        coefficientSequenceLimit l E Y ⋙ podCompletedDerivedInverseImage l E g,
      PodLimitResolutionNormalization l E g e ∧
      ∀ (N : coefficientSequenceDerived l E Y) (n : ℕ),
        e.hom.app N ≫ (podCompletedDerivedInverseImage l E g).map
          ((coefficientSequenceProjection l E Y n).app N) =
        (coefficientSequenceProjection l E X n).app
          ((pullbackTensorSequenceDerived l E g).obj N) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((pullbackTensorDerivedEvaluation l E g n).hom.app N) ≫
        (podFiniteRestriction l E g n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  sorry

/-- The total derived-limit comparison fixed by resolutions and projections.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podLimitReindexing := (podLimitReindexing_existsUnique l E g).exists.choose
end CompletedReindexing


section ReductionNormalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- The canonical reduction/reindexing map: the actual reduction/limit adjunct
of exact inverse image of the unit, followed by the inverse limit comparison.
Source: node proof steps 8 and 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podReductionReindexingMap (K : DerivedCategory (integralTowerModules l E Y)) :
    (pullbackTensorCalculus l E X).reduction.obj
        ((podCompletedDerivedInverseImage l E g).obj K) ⟶
      (pullbackTensorSequenceDerived l E g).obj
        ((pullbackTensorCalculus l E Y).reduction.obj K) :=
  ((pullbackTensorCalculus l E X).adjunction.homEquiv _ _).symm
    ((podCompletedDerivedInverseImage l E g).map
        ((pullbackTensorCalculus l E Y).adjunction.unit.app K) ≫
      (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj K))

/-- The canonical reduction adjunct is invertible and natural for every ambient
complex, without asserting invertibility of the completion unit.
Source: node proof steps 8 and 13.
Proof: the two reduction functors are ordinary quotient systems on a flat-term
K-flat representative. Reindexing commutes with every quotient and strict
transition. Their identity-on-sections map is the displayed adjunct, by the
actual reduction unit and projection equations. Inverse reindexing gives an
inverse system map before localization. Naturality holds on representatives
and descends to every derived arrow.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podReductionReindexingMap_laws :
    (∀ K, IsIso (podReductionReindexingMap l E g K)) ∧
    ∀ (K L : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ L),
      (pullbackTensorCalculus l E X).reduction.map
          ((podCompletedDerivedInverseImage l E g).map f) ≫
        podReductionReindexingMap l E g L =
      podReductionReindexingMap l E g K ≫
        (pullbackTensorSequenceDerived l E g).map
          ((pullbackTensorCalculus l E Y).reduction.map f) := by
  sorry

/-- The reduction comparison is the isomorphism of that very canonical adjunct.
Source: node proof step 13 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podReductionReindexing (K : DerivedCategory (integralTowerModules l E Y)) :=
  @asIso _ _ _ _ (podReductionReindexingMap l E g K)
    ((podReductionReindexingMap_laws l E g).1 K)

/-- Exact inverse image to tower pullback: inverse image of the actual completion
unit, the inverse total-limit comparison, and the inverse recorded Roos model.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedToTower (K : DerivedCategory (integralTowerModules l E Y)) :
    (podCompletedDerivedInverseImage l E g).obj K ⟶ (integralDerivedPullback l E g).obj K :=
  (podCompletedDerivedInverseImage l E g).map
      ((pullbackTensorCalculus l E Y).adjunction.unit.app K) ≫
    (podLimitReindexing l E g).inv.app ((pullbackTensorCalculus l E Y).reduction.obj K) ≫
    (pullbackTensorIntegralPullbackModel l E g).inv.app K

/-- The identification with tower-defined pullback is natural, and is invertible
on exactly the complete constructible inputs used here.
Source: node proof step 8.
Proof: all three factors are natural. For a constructible complete K, the
canonical quotient-tower unit is invertible by the finite-free completed
scalar theorem for E/E. The other two factors are isomorphisms already.
The total-limit comparison's resolution and projection equations imply
commutation with every reduction projection.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedToTower_laws :
    (∀ (K L : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ L),
      (podCompletedDerivedInverseImage l E g).map f ≫ podCompletedToTower l E g L =
        podCompletedToTower l E g K ≫ (integralDerivedPullback l E g).map f) ∧
    (∀ K : sfIntegralConstructibleCategory l E Y, IsIso (podCompletedToTower l E g K.obj)) := by
  sorry

/-- The canonical complete-input identification, retaining its specified map.
Source: node proof step 8 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedToTowerIso (K : sfIntegralConstructibleCategory l E Y) :=
  @asIso _ _ _ _ (podCompletedToTower l E g K.obj) ((podCompletedToTower_laws l E g).2 K)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The integral Hom comparison expressed through the exact completed-ring
inverse image, with the canonical complete-input identifications inserted.
Source: node proof steps 8, 11, 13
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralReindexedHom (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    (podCompletedDerivedInverseImage l E g).obj
        ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj)) ⟶
      (integralDerivedInternalHom l E X).obj
        (op ((podCompletedDerivedInverseImage l E g).obj P.obj.1.unop.obj),
          (podCompletedDerivedInverseImage l E g).obj P.obj.2.obj) :=
  (podCompletedToTowerIso l E g ((constructibleIntegralHom l E Y).obj P)).hom ≫
    (podIntegralHomComparison l E g P).hom ≫
    (integralDerivedInternalHom l E X).map
      (Prod.mkHom (podCompletedToTowerIso l E g P.obj.1.unop).hom.op
        (podCompletedToTowerIso l E g P.obj.2).inv)

/-- The reduction/internal-Hom comparison square commutes as an actual derived
system square, hence also under the specified functorial total-limit realization.
Source: node proof step 13.
Proof: beta is the transpose of reduced evaluation on one simultaneous system
resolution. Reindexing carries that evaluation and its transpose to the same
chain map. The reduction/reindexing maps are its actual unit adjuncts, so
unit/counit identities identify the two composites before localization.
The normalized integral closed equation extends the same evaluation across
completion, giving the displayed top map. Apply the functorial total limit
to obtain the realized square and its evaluation/transposition identities.
This uses neither equality detection by evaluations nor invertibility of beta.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podHomReductionSquare
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    (pullbackTensorCalculus l E X).reduction.map (podIntegralReindexedHom l E g P) ≫
      coefficientBaseChangeHom (pullbackTensorCalculus l E X).integralClosed
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).reduction (pullbackTensorCalculus l E X).reductionTensor
        ((podCompletedDerivedInverseImage l E g).obj P.obj.1.unop.obj)
        ((podCompletedDerivedInverseImage l E g).obj P.obj.2.obj) =
    (podReductionReindexing l E g
      ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj))).hom ≫
      (pullbackTensorSequenceDerived l E g).map
        (coefficientBaseChangeHom (pullbackTensorCalculus l E Y).integralClosed
          (pullbackTensorCalculus l E Y).systemClosed (pullbackTensorCalculus l E Y).reduction
          (pullbackTensorCalculus l E Y).reductionTensor P.obj.1.unop.obj P.obj.2.obj) ≫
      podSystemHomComparison l E g
        ((pullbackTensorCalculus l E Y).reduction.obj P.obj.1.unop.obj)
        ((pullbackTensorCalculus l E Y).reduction.obj P.obj.2.obj) ≫
      (coefficientSequenceInternalHom l E X).map
        (Prod.mkHom (podReductionReindexing l E g P.obj.1.unop.obj).hom.op
          (podReductionReindexing l E g P.obj.2.obj).inv) := by
  sorry
end ReductionNormalization

section SignedShifts
universe r s t w
variable {C : Type s} [Category.{t} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max s t r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max s t r}]
  (A : Sheaf J CommRingCat.{max s t r})

/-- Modules in the existing independent-universe coefficient convention.
Source: Stacks 08J9 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
abbrev PodModules := SheafOfModules.{max s t r}
  ((sheafCompose J (forget₂ CommRingCat.{max s t r} RingCat.{max s t r})).obj A)

/-- The canonical signed Hom-complex shift, fixed by every product projection.
Source: node proof step 6, Stacks 08JA.
Proof: reindex the product from p to p+m and multiply degree k by (-1)^(m*k).
The adjacent-degree signs compensate the shifted differential. The inverse
reindexes by -m with the inverse sign, so the map is an isomorphism. Product
projections are jointly monic, proving uniqueness, including negative shifts.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podHomComplexShift_existsUnique
    (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) (m n : ℤ) :
    ∃! e : (homComplex.{s, t, max s t r, max s t r} (R := A) K I)⟦n - m⟧ ≅
        homComplex.{s, t, max s t r, max s t r} (R := A) (K⟦m⟧) (I⟦n⟧),
      ∀ (k p q : ℤ) (h : p + k = q) (h' : p + m + (k + (n - m)) = q + n),
        e.hom.f k ≫ coefficientHomComponent.{r, s, t} J A (K⟦m⟧) (I⟦n⟧) k p q h =
          (m * k).negOnePow •
            ((homComplex.{s, t, max s t r, max s t r} (R := A) K I).shiftFunctorObjXIso
                (n - m) k (k + (n - m)) rfl).hom ≫
            coefficientHomComponent.{r, s, t} J A K I (k + (n - m)) (p + m) (q + n) h' ≫
            SheafOfModules.homObjMap.{max s t r, t, s, max s t r}
              (K.shiftFunctorObjXIso m p (p + m) rfl).hom
              (I.shiftFunctorObjXIso n q (q + n) rfl).inv := by
  sorry

/-- The unique signed product-reindexing map.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podHomComplexShift (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) (m n : ℤ) :=
  (podHomComplexShift_existsUnique.{r, s, t} J A K I m n).exists.choose

variable [HasDerivedCategory.{w} (PodModules.{r, s, t} J A)]

/-- The actual augmentation of the chosen Hom target resolution.
Source: Stacks 0A95 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podHomAugmentation (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) :
    homComplex.{s, t, max s t r, max s t r} (R := A) K I ⟶
      homComplex.{s, t, max s t r, max s t r} (R := A) K
        ((coefficientHomResolution.{r, s, t} J A).obj I) :=
  letI :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{s, t, r}
      J A).1
  (homComplexFunctor.{s, t, max s t r, max s t r}.obj (op K)).map
    ((CochainComplex.toKInjectiveResolution _).app I)

/-- The K-injective representative model is fixed by the actual augmentation.
Source: Stacks 0A95, node proof steps 3 and 6.
Proof: for K-injective I, its augmentation to the fixed resolution is a homotopy
 equivalence between K-injectives. Hom(K,-) preserves its homotopy inverse.
Localize and invert that map in the recorded resolution factorization. The
normalization determines the isomorphism uniquely by cancellation.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podKInjectiveHomModel_existsUnique
    (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) [I.IsKInjective] :
    ∃! e : (derivedInternalHomOfUniverses.{s, t, r, w} J A).obj
        (op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I) ≅
          DerivedCategory.Q.obj (homComplex.{s, t, max s t r, max s t r} (R := A) K I),
      e.hom ≫ DerivedCategory.Q.map (podHomAugmentation.{r, s, t} J A K I) =
        (coefficientHomResolutionIso.{r, s, t, w} J A K I).hom := by
  sorry

/-- Canonical K-injective representative comparison.
Source: Stacks 0A95 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podKInjectiveHomModel
    (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) [I.IsKInjective] :=
  (podKInjectiveHomModel_existsUnique.{r, s, t, w} J A K I).exists.choose

/-- The canonical cohomological shift identifications, with their precise
signed representative normalization; no universe equality is imposed.
Source: node proof step 6, Stacks 08JA.
Proof: localize the signed Hom-complex shift on K-injective targets and insert
its canonical representative comparisons. Shifts preserve K-injectives. The
formula is natural in both chain arguments and preserves homotopies, hence
descends to arbitrary derived arrows. Every object has such a representative,
so naturality and the representative equation determine the family uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podDerivedHomShift_existsUnique :
    ∃! σ : ∀ (M N : DerivedCategory (PodModules.{r, s, t} J A)) (m n : ℤ),
        ((derivedInternalHomOfUniverses.{s, t, r, w} J A).obj (op M, N))⟦n - m⟧ ≅
          (derivedInternalHomOfUniverses.{s, t, r, w} J A).obj (op (M⟦m⟧), N⟦n⟧),
      (∀ (M N M' N' : DerivedCategory (PodModules.{r, s, t} J A)) (m n : ℤ)
        (f : M' ⟶ M) (h : N ⟶ N'),
        ((derivedInternalHomOfUniverses.{s, t, r, w} J A).map (Prod.mkHom f.op h))⟦n - m⟧' ≫
            (σ M' N' m n).hom =
          (σ M N m n).hom ≫ (derivedInternalHomOfUniverses.{s, t, r, w} J A).map
            (Prod.mkHom (f⟦m⟧').op (h⟦n⟧'))) ∧
      ∀ (K I : CochainComplex (PodModules.{r, s, t} J A) ℤ) [I.IsKInjective] (m n : ℤ),
        (σ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj I) m n).hom ≫
            (derivedInternalHomOfUniverses.{s, t, r, w} J A).map
              (Prod.mkHom ((DerivedCategory.Q.commShiftIso m).hom.app K).op
                ((DerivedCategory.Q.commShiftIso n).inv.app I)) ≫
            (podKInjectiveHomModel.{r, s, t, w} J A (K⟦m⟧) (I⟦n⟧)).hom =
          ((podKInjectiveHomModel.{r, s, t, w} J A K I).hom)⟦n - m⟧' ≫
            (DerivedCategory.Q.commShiftIso (n - m)).inv.app
              (homComplex.{s, t, max s t r, max s t r} (R := A) K I) ≫
            DerivedCategory.Q.map (podHomComplexShift.{r, s, t} J A K I m n).hom := by
  sorry

/-- The signed canonical shift comparison, fixed on representatives above.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podDerivedHomShift := (podDerivedHomShift_existsUnique.{r, s, t, w} J A).exists.choose
end SignedShifts

section FiniteCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The finite signed shift identification is the fixed representative map.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteHomShift (W : Scheme.{u}) (n : ℕ) :=
  podDerivedHomShift.{u, u+1, u} (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)

/-- The comparison commutes with shifts in both arguments, in every integer degree.
Source: node proof step 6, Stacks 08JA.
Proof: exact inverse image acts termwise and preserves the Hom product projections.
It preserves the sign (-1)^(m*k) and reindexing p to p+m in the defining shift map.
Thus the equality holds on the signed Hom complexes. Insert the canonical
K-injective models and exact pullback shift comparisons, then localize.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteHomComparison_shift (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) (a b : ℤ) :
    (podFiniteHomComparison l E g n M N)⟦b - a⟧' ≫
        (podFiniteHomShift l E X n
          ((finiteDerivedPullback l E n g).obj M)
          ((finiteDerivedPullback l E n g).obj N) a b).hom =
      ((finiteDerivedPullback l E n g).commShiftIso (b - a)).inv.app
          ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) ≫
        (finiteDerivedPullback l E n g).map (podFiniteHomShift l E Y n M N a b).hom ≫
        podFiniteHomComparison l E g n (M⟦a⟧) (N⟦b⟧) ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map
          (Prod.mkHom (((finiteDerivedPullback l E n g).commShiftIso a).inv.app M).op
            (((finiteDerivedPullback l E n g).commShiftIso b).hom.app N)) := by
  sorry

/-- The canonical scheme-composition comparison, induced by intrinsic pullback's
published composition and exact derived factorization.
Source: node proof step 7 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFinitePullbackComp (h : Z ⟶ X) (n : ℕ) :
    finiteDerivedPullback l E n (h ≫ g) ≅
      finiteDerivedPullback l E n g ⋙ finiteDerivedPullback l E n h :=
  Functor.mapDerivedCategoryNatIso
      (sfIntrinsicPullbackComp (finiteCoefficientRing l E (n + 1)) h g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Hom comparisons commute with composition of scheme isomorphisms.
Source: node proof step 7, Stacks 0GMX.
Proof: on sections, inverse image under a composite reindexes by the composite
site functor. Both Hom maps send a local homomorphism to this same reindexed
homomorphism. The published pullback comparison is exactly the unit-normalized
reindexing comparison. Tensor and evaluation have the same composition rule.
Taking their closed transposes gives the equation, before localization and
therefore in the unbounded derived category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podFiniteHomComparison_comp (h : Z ⟶ X) [IsIso h]
    [∀ z : Z, Invertible (l : Z.residueField z)] (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (podFinitePullbackComp l E g h n).hom.app
          ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N)) ≫
        (finiteDerivedPullback l E n h).map (podFiniteHomComparison l E g n M N) ≫
        podFiniteHomComparison l E h n
          ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
      podFiniteHomComparison l E (h ≫ g) n M N ≫
        (finiteIntrinsicDerivedInternalHom l E Z n).map
          (Prod.mkHom ((podFinitePullbackComp l E g h n).inv.app M).op
            ((podFinitePullbackComp l E g h n).hom.app N)) := by
  sorry
end FiniteCoherence

section IntegralShiftCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Ambient completed-ring Hom has the same signed representative shift.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralAmbientHomShift (W : Scheme.{u}) :=
  podDerivedHomShift.{u, u+1, u} (ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

/-- The permitted integral pairs are stable under both argument shifts.
Source: node proof step 6, Stacks 08JA.
Proof: shift stability of the constructible subcategory gives both inputs.
The signed ambient Hom shift identifies the new Hom with a shift of the old
constructible Hom; shift stability and isomorphism closure give its property.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPair_shift_property
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    constructibleIntegralHomPairs l E Y (op (P.obj.1.unop⟦a⟧), P.obj.2⟦b⟧) := by
  sorry

/-- The actual shifted pair, with its established Hom constructibility.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralShiftPair
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    (constructibleIntegralHomPairs l E Y).FullSubcategory :=
  ⟨(op (P.obj.1.unop⟦a⟧), P.obj.2⟦b⟧), podIntegralPair_shift_property l E P a b⟩

/-- Shift compatibility in exact completed-ring coordinates. Conjugating by the
canonical completion-unit comparison gives the tower-defined integral square.
Source: node proof steps 6, 8 and 11.
Proof: reindexing preserves every signed Hom projection exactly as at finite
coefficients. The complete-input comparison and its reduction/limit adjunct
are maps of exact functors and commute with these shifts. Insert their
normalizations in the signed representative equality. The restricted Hom
pair shift is the same ambient shift, so the displayed equation results.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralReindexedHom_shift
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    (podIntegralReindexedHom l E g P)⟦b - a⟧' ≫
        (podIntegralAmbientHomShift l E X
          ((podCompletedDerivedInverseImage l E g).obj P.obj.1.unop.obj)
          ((podCompletedDerivedInverseImage l E g).obj P.obj.2.obj) a b).hom =
      ((podCompletedDerivedInverseImage l E g).commShiftIso (b - a)).inv.app
          ((integralDerivedInternalHom l E Y).obj (op P.obj.1.unop.obj, P.obj.2.obj)) ≫
        (podCompletedDerivedInverseImage l E g).map
          (podIntegralAmbientHomShift l E Y P.obj.1.unop.obj P.obj.2.obj a b).hom ≫
        (podCompletedDerivedInverseImage l E g).map
          ((integralDerivedInternalHom l E Y).map
            (Prod.mkHom (((sfIntegralConstructible l E Y).ι.commShiftIso a).hom.app
              P.obj.1.unop).op
              (((sfIntegralConstructible l E Y).ι.commShiftIso b).inv.app P.obj.2))) ≫
        podIntegralReindexedHom l E g (podIntegralShiftPair l E P a b) ≫
        (integralDerivedInternalHom l E X).map
          (Prod.mkHom ((((podCompletedDerivedInverseImage l E g).commShiftIso a).inv.app
              P.obj.1.unop.obj) ≫ (podCompletedDerivedInverseImage l E g).map
                (((sfIntegralConstructible l E Y).ι.commShiftIso a).inv.app P.obj.1.unop)).op
            ((podCompletedDerivedInverseImage l E g).map
                (((sfIntegralConstructible l E Y).ι.commShiftIso b).hom.app P.obj.2) ≫
              ((podCompletedDerivedInverseImage l E g).commShiftIso b).hom.app P.obj.2.obj)) := by
  sorry
end IntegralShiftCoherence

section IntegralComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]

/-- Composition of exact completed inverse image is fixed on all local sections.
Source: node proof steps 1 and 7, Stacks 00WX.
Proof: composition of the two postcomposition functors agrees with postcomposition
by the composite, using associativity of scheme arrows. The identity on the
unchanged local sections is linear because both coefficient transports have
identical finite projections. It is a natural isomorphism; pointwise equality
on all local sections proves uniqueness.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCompletedModuleComp_existsUnique :
    ∃! e : podCompletedModuleInverseImage l E (h ≫ g) ≅
        podCompletedModuleInverseImage l E g ⋙ podCompletedModuleInverseImage l E h,
      ∀ (M : integralTowerModules l E Y) (U : Z.ProEt)
        (x : ((podCompletedModuleInverseImage l E (h ≫ g)).obj M).val.obj (op U)),
        HEq (((e.hom.app M).val.app (op U)) x) x := by
  sorry

/-- The unique identity-on-sections completed composition comparison.
Source: Stacks 00WX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedModuleComp := (podCompletedModuleComp_existsUnique l E g h).exists.choose

/-- Derive that same ordinary comparison, using the fixed exact factorizations.
Source: node proof steps 2 and 7
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podCompletedDerivedComp : podCompletedDerivedInverseImage l E (h ≫ g) ≅
    podCompletedDerivedInverseImage l E g ⋙ podCompletedDerivedInverseImage l E h :=
  letI := podCompletedModuleAdditive l E g
  letI := podCompletedModuleAdditive l E h
  letI := podCompletedModuleAdditive l E (h ≫ g)
  letI := podCompletedModuleLimits l E g
  letI := podCompletedModuleLimits l E h
  letI := podCompletedModuleLimits l E (h ≫ g)
  letI := podCompletedModuleColimits l E g
  letI := podCompletedModuleColimits l E h
  letI := podCompletedModuleColimits l E (h ≫ g)
  Functor.mapDerivedCategoryNatIso (podCompletedModuleComp l E g h) ≪≫
    Functor.mapDerivedCategoryCompIso (podCompletedModuleInverseImage l E g)
      (podCompletedModuleInverseImage l E h)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Published integral tower composition has the actual completion-unit normalization.
Source: node proof steps 7--8.
Proof: conjugate the derived identity-on-sections composition by the three
complete-input identifications. Their maps are fixed by completion units and
total-limit reindexing. Hence this is the canonical tower composition, natural
by their naturality. Its component formula determines it uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPullbackComp_normalization
    (M : sfIntegralConstructibleCategory l E Y) :
    HEq (((pullbackTensorIntegralComposition l E g h).hom.app M).hom)
      ((podCompletedToTowerIso l E (h ≫ g) M).inv ≫
        (podCompletedDerivedComp l E g h).hom.app M.obj ≫
        (podCompletedDerivedInverseImage l E h).map (podCompletedToTowerIso l E g M).hom ≫
        (podCompletedToTowerIso l E h ((constructibleIntegralPullback l E g).obj M)).hom) := by
  sorry

/-- Integral comparisons commute with composition, using canonical tower composition.
Source: node proof steps 7, 8 and 11.
Proof: reindexing Hom twice equals reindexing once by the composite on each
product projection. Its evaluation formula therefore agrees before localization.
Conjugate by the completion-unit comparisons. Their normalization gives exactly
the displayed composition maps, including the contravariant first argument.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomComparison_comp
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) :
    (pullbackTensorIntegralComposition l E g h).hom.app ((constructibleIntegralHom l E Y).obj P) ≫
        (constructibleIntegralPullback l E h).map (podIntegralHomComparison l E g P) ≫
        podIntegralHomComparison l E h
          ((podPairPullback (constructibleIntegralPullback l E g) _ _
            (podIntegralPairs_pullback l E g)).obj P) =
      podIntegralHomComparison l E (h ≫ g) P ≫
        (constructibleIntegralHom l E Z).map
          (ObjectProperty.homMk
            (X := (podPairPullback (constructibleIntegralPullback l E (h ≫ g)) _ _
              (podIntegralPairs_pullback l E (h ≫ g))).obj P)
            (Y := (podPairPullback (constructibleIntegralPullback l E h) _ _
              (podIntegralPairs_pullback l E h)).obj
                ((podPairPullback (constructibleIntegralPullback l E g) _ _
                  (podIntegralPairs_pullback l E g)).obj P))
            (Prod.mkHom ((pullbackTensorIntegralComposition l E g h).inv.app P.obj.1.unop).op
              ((pullbackTensorIntegralComposition l E g h).hom.app P.obj.2))) := by
  sorry
end IntegralComposition

section SystemFibers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]

/-- Reindexing preserves normalized coefficient systems, including all transitions.
Source: node proof step 12, Stacks 0941.
Proof: reindex the simultaneous flat-term system representative. Each quotient
comparison is the unit-normalized finite inverse image, and every transition
is unchanged. Reindexing the inverse data gives normalization of the result.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemNormalized (M : coefficientSequenceDerived l E Y)
    (hM : IsNormalizedCoefficientSequence l E Y M) :
    IsNormalizedCoefficientSequence l E X ((pullbackTensorSequenceDerived l E g).obj M) := by
  sorry

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The actual system Hom comparison has the prescribed finite fibers.
Source: node proof steps 12--13.
Proof: on one simultaneous normalized system model, evaluate the Hom-product
reindexing chain map. Its projections are precisely the finite Hom reindexing
map. The fiber maps are induced by that same evaluation and transposition,
not independent choices. Their representative equations yield this square in
the finite derived category; the original equality of system maps was already
established before any evaluation.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_fiber
    (M N : coefficientSequenceDerived l E Y)
    (hM : IsNormalizedCoefficientSequence l E Y M)
    (hN : IsNormalizedCoefficientSequence l E Y N) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).map (podSystemHomComparison l E g M N) ≫
        ((pullbackTensorCalculus l E X).fiberHom
          ((pullbackTensorSequenceDerived l E g).obj M)
          ((pullbackTensorSequenceDerived l E g).obj N)
          (podSystemNormalized l E g M hM) (podSystemNormalized l E g N hN) n).hom =
      (pullbackTensorDerivedEvaluation l E g n).hom.app
          ((coefficientSequenceInternalHom l E Y).obj (op M, N)) ≫
        (finiteDerivedPullback l E n g).map
          ((pullbackTensorCalculus l E Y).fiberHom M N hM hN n).hom ≫
        podFiniteHomComparison l E g n
          ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
          ((coefficientSequenceDerivedEvaluation l E Y n).obj N) ≫
        (finiteIntrinsicDerivedInternalHom l E X n).map
          (Prod.mkHom ((pullbackTensorDerivedEvaluation l E g n).hom.app M).op
            ((pullbackTensorDerivedEvaluation l E g n).inv.app N)) := by
  sorry

/-- The system evaluation identity holds in its functorial total-limit realization.
Source: node proof steps 12--13.
Proof: apply the functorial derived limit to the already established system
map equality. Functoriality preserves its composites. The specified total-limit
models identify these images with the realized evaluation maps; no equality
reflection from separately evaluated levels occurs.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podSystemHomComparison_realizedEvaluation
    (M N : coefficientSequenceDerived l E Y) :
    (coefficientSequenceLimit l E X).map
      ((pullbackTensorSystemComparison l E g).hom.app
          ((coefficientSequenceInternalHom l E Y).obj (op M, N), M) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom (podSystemHomComparison l E g M N) (𝟙 _)) ≫
        (pullbackTensorCalculus l E X).systemClosed.evaluation
          ((pullbackTensorSequenceDerived l E g).obj M)
          ((pullbackTensorSequenceDerived l E g).obj N)) =
      (coefficientSequenceLimit l E X).map
        ((pullbackTensorSequenceDerived l E g).map
          ((pullbackTensorCalculus l E Y).systemClosed.evaluation M N)) := by
  sorry
end SystemFibers

/-- The argument-first evaluation convention of the statement, obtained by the
specified Koszul symmetry from the recorded Hom-first closed structure.
Source: Stacks 08J9 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podArgumentFirstEvaluation {C : Type a} [Category.{b} C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H)
    (β : ∀ M N : C, T.obj (M, N) ≅ T.obj (N, M)) (P : J.FullSubcategory) :=
  (β P.obj.1.unop (H.obj P)).hom ≫ S.evaluation P

/-- Evaluation and every transpose in exactly the argument-first convention.
Source: Stacks 0GMX (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def PodArgumentFirstLaws {C : Type a} {D : Type c}
    [Category.{b} C] [Category.{d} D] [Preadditive C] [Preadditive D]
    {TC : C × C ⥤ C} {TD : D × D ⥤ D}
    {J : ObjectProperty (Cᵒᵖ × C)} {K : ObjectProperty (Dᵒᵖ × D)}
    {HC : J.FullSubcategory ⥤ C} {HD : K.FullSubcategory ⥤ D}
    (SC : PodPartialClosed TC J HC) (SD : PodPartialClosed TD K HD)
    (F : C ⥤ D) (h : ∀ P : J.FullSubcategory, K ((F.op.prod F).obj P.obj))
    (μ : ∀ L M : C, F.obj (TC.obj (L, M)) ≅ TD.obj (F.obj L, F.obj M))
    (βC : ∀ M N : C, TC.obj (M, N) ≅ TC.obj (N, M))
    (βD : ∀ M N : D, TD.obj (M, N) ≅ TD.obj (N, M)) : Prop :=
  (∀ P : J.FullSubcategory,
    (μ P.obj.1.unop (HC.obj P)).hom ≫
      TD.map (Prod.mkHom (𝟙 _) (podPartialHomComparison SC SD F h μ P)) ≫
      podArgumentFirstEvaluation SD βD ((podPairPullback F J K h).obj P) =
    F.map (podArgumentFirstEvaluation SC βC P)) ∧
  ∀ (L : C) (P : J.FullSubcategory) (b : TC.obj (P.obj.1.unop, L) ⟶ P.obj.2),
    SD.transpose _ _ ((βD (F.obj L) (F.obj P.obj.1.unop)).hom ≫
        (μ P.obj.1.unop L).inv ≫ F.map b) =
      F.map (SC.transpose L P ((βC L P.obj.1.unop).hom ≫ b)) ≫
        podPartialHomComparison SC SD F h μ P

section ArgumentFirstStages
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Integral and rational equations in the node's argument-first convention.
Source: node proof steps 4--5, 11 and 14.
Proof: precompose the Hom-first evaluation equation with the canonical Koszul
braiding. Its naturality moves c to the second factor; tensor pullback respects
this braiding by the published signed comparison equation. Transpose after
the same swap. Localization preserves these composites and their identities.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_integral_rational :
    PodArgumentFirstLaws (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g)
      (pullbackTensorIntegralBraiding l E Y) (pullbackTensorIntegralBraiding l E X) ∧
    PodArgumentFirstLaws (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g)
      (pullbackTensorRationalBraiding l E Y) (pullbackTensorRationalBraiding l E X) := by
  sorry

/-- Finite evaluation with argument first is the actual signed swap followed by
recorded evaluation. Source: node proof step 4
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podFiniteArgumentFirstEvaluation (W : Scheme.{u}) (n : ℕ)
    (M N : proEtaleDerivedCategory W (finiteCoefficientRing l E (n + 1))) :=
  (pullbackTensorBraiding (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)
      (finiteIntrinsicClosed l E W n) (finiteIntrinsicTensorModels l E W n)).hom.app
      (M, (finiteIntrinsicDerivedInternalHom l E W n).obj (op M, N)) ≫
    finiteIntrinsicEvaluation l E W n M N

/-- The finite argument-first evaluation equation is the displayed equation of
the node. Source: node proof steps 4--5.
Proof: combine the Hom-first equation with signed braiding naturality and its
published tensor-pullback square. Both paths evaluate the same local map on
the same local section, including the Koszul sign on homogeneous complexes.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_finite (n : ℕ)
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (canonicalFinitePullbackTensor l E g n M
        ((finiteIntrinsicDerivedInternalHom l E Y n).obj (op M, N))).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 _) (podFiniteHomComparison l E g n M N)) ≫
      podFiniteArgumentFirstEvaluation l E X n
        ((finiteDerivedPullback l E n g).obj M) ((finiteDerivedPullback l E n g).obj N) =
    (finiteDerivedPullback l E n g).map (podFiniteArgumentFirstEvaluation l E Y n M N) := by
  sorry
/-- The finite transpose equation with the tensor arguments in the node's order.
Source: node proof steps 4--5.
Proof: swap the two tensor factors by their fixed signed braiding, apply finite
transposition, and use the tensor-pullback braiding square. The two swaps give
exactly the argument-first adjunction, so currying yields the displayed map.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_finite_transpose (n : ℕ)
    (L M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)))
    (b : (finiteIntrinsicDerivedTensor l E Y n).obj (M, L) ⟶ N) :
    finiteIntrinsicTranspose l E X n _ _ _
      ((pullbackTensorBraiding (ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)
          (finiteIntrinsicClosed l E X n) (finiteIntrinsicTensorModels l E X n)).hom.app
          ((finiteDerivedPullback l E n g).obj L, (finiteDerivedPullback l E n g).obj M) ≫
        (canonicalFinitePullbackTensor l E g n M L).inv ≫
        (finiteDerivedPullback l E n g).map b) =
      (finiteDerivedPullback l E n g).map
        (finiteIntrinsicTranspose l E Y n L M N
          ((pullbackTensorBraiding (ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)
              (finiteIntrinsicClosed l E Y n) (finiteIntrinsicTensorModels l E Y n)).hom.app
              (L, M) ≫ b)) ≫
        podFiniteHomComparison l E g n M N := by
  sorry
end ArgumentFirstStages

section ArgumentFirstCommon
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The displayed argument-first equations at algebraically closed coefficients.
Source: node proof step 16.
Proof: put the inputs and each arrow over one finite field. The prescribed
common braiding, tensor comparison and transpose are the rational maps there.
Apply the rational argument-first equations. Their scalar compatibility gives
the equality in the actual common-stage Hom group, for every representative.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podArgumentFirst_common :
    PodArgumentFirstLaws (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g)
      (pullbackTensorCommonBraiding l Ω Y) (pullbackTensorCommonBraiding l Ω X) := by
  sorry
end ArgumentFirstCommon

section FieldComposition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Composition at E uses the published localized integral composition maps.
Source: node proof steps 7 and 14.
Proof: localize the integral composition equation. Every comparison component
and composition identification is the prescribed localized component. The
localization functor preserves composites, hence gives the displayed equality.
No restriction on localized arrows enters, since naturality is additive and
balanced and already holds for all of them.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podRationalHomComparison_comp
    (P : (constructibleRationalHomPairs l E Y).FullSubcategory) :
    (pullbackTensorRationalComposition l E g h
        ((rationalDerivedInternalHom l E Y).obj P)).hom ≫
        (rationalDerivedPullback l E h).map (podRationalHomComparison l E g P) ≫
        podRationalHomComparison l E h
          ((podPairPullback (rationalDerivedPullback l E g) _ _
            (podRationalPairs_pullback l E g)).obj P) =
      podRationalHomComparison l E (h ≫ g) P ≫
        (rationalDerivedInternalHom l E Z).map
          (ObjectProperty.homMk
            (X := (podPairPullback (rationalDerivedPullback l E (h ≫ g)) _ _
              (podRationalPairs_pullback l E (h ≫ g))).obj P)
            (Y := (podPairPullback (rationalDerivedPullback l E h) _ _
              (podRationalPairs_pullback l E h)).obj
                ((podPairPullback (rationalDerivedPullback l E g) _ _
                  (podRationalPairs_pullback l E g)).obj P))
            (Prod.mkHom (pullbackTensorRationalComposition l E g h P.obj.1.unop).inv.op
              (pullbackTensorRationalComposition l E g h P.obj.2).hom)) := by
  sorry
end FieldComposition

section CommonComposition
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y Z : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (h : Z ⟶ X) [IsIso h]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ z : Z, Invertible (l : Z.residueField z)]

/-- Common-stage composition holds in the actual Hom-colimit category.
Source: node proof steps 7 and 16.
Proof: use a common finite coefficient stage for the pair, comparisons and
composition arrows. The specified common-stage transpose and tensor comparison
identify c with the rational c. The published common composition is represented
by the rational composition. Apply the rational equation and take its class;
scalar-extension compatibility makes this independent of all enlargements.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_comp
    (P : (commonStageHomPairs l Ω Y).FullSubcategory) :
    (pullbackTensorCommonComposition l Ω g h
        ((commonStageDerivedInternalHom l Ω Y).obj P)).hom ≫
        (commonStageDerivedPullback l Ω h).map (podCommonHomComparison l Ω g P) ≫
        podCommonHomComparison l Ω h
          ((podPairPullback (commonStageDerivedPullback l Ω g) _ _
            (podCommonPairs_pullback l Ω g)).obj P) =
      podCommonHomComparison l Ω (h ≫ g) P ≫
        (commonStageDerivedInternalHom l Ω Z).map
          (ObjectProperty.homMk
            (X := (podPairPullback (commonStageDerivedPullback l Ω (h ≫ g)) _ _
              (podCommonPairs_pullback l Ω (h ≫ g))).obj P)
            (Y := (podPairPullback (commonStageDerivedPullback l Ω h) _ _
              (podCommonPairs_pullback l Ω h)).obj
                ((podPairPullback (commonStageDerivedPullback l Ω g) _ _
                  (podCommonPairs_pullback l Ω g)).obj P))
            (Prod.mkHom (pullbackTensorCommonComposition l Ω g h P.obj.1.unop).inv.op
              (pullbackTensorCommonComposition l Ω g h P.obj.2).hom)) := by
  sorry
end CommonComposition

section RestrictedShiftMaps
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Restrict the canonical signed ambient Hom shift to the permitted pairs.
Source: node proof step 6, Stacks 08JA.
Proof: all three objects are constructible by shift closure and the shifted-pair
property. The inclusion is fully faithful, so the displayed ambient isomorphism
and its inverse lift uniquely. The inclusion shift comparison reconciles its
chosen shift object with the ambient shifted complex.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralHomShift_existsUnique
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    ∃! e : ((constructibleIntegralHom l E Y).obj P)⟦b - a⟧ ≅
        (constructibleIntegralHom l E Y).obj (podIntegralShiftPair l E P a b),
      e.hom.hom = ((sfIntegralConstructible l E Y).ι.commShiftIso (b - a)).hom.app
          ((constructibleIntegralHom l E Y).obj P) ≫
        (podIntegralAmbientHomShift l E Y P.obj.1.unop.obj P.obj.2.obj a b).hom ≫
        (integralDerivedInternalHom l E Y).map
          (Prod.mkHom (((sfIntegralConstructible l E Y).ι.commShiftIso a).hom.app
            P.obj.1.unop).op
            (((sfIntegralConstructible l E Y).ι.commShiftIso b).inv.app P.obj.2)) := by
  sorry

/-- The restricted signed Hom shift, with its actual ambient normalization.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralHomShift
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :=
  (podIntegralHomShift_existsUnique l E P a b).exists.choose

/-- Pullback's shift comparison is fixed through the canonical complete-input map.
Source: node proof steps 2, 6 and 8.
Proof: conjugate the termwise exact inverse-image shift by the completion-unit
identification, and then by the full-subcategory inclusion's shift comparison.
Naturality and the shift zero/addition equations are inherited from those
comparisons. The displayed equation fixes the isomorphism uniquely.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralPullbackShift_existsUnique
    (M : sfIntegralConstructibleCategory l E Y) (a : ℤ) :
    ∃! e : (constructibleIntegralPullback l E g).obj (M⟦a⟧) ≅
        ((constructibleIntegralPullback l E g).obj M)⟦a⟧,
      e.hom.hom = (podCompletedToTowerIso l E g (M⟦a⟧)).inv ≫
        (podCompletedDerivedInverseImage l E g).map
          (((sfIntegralConstructible l E Y).ι.commShiftIso a).hom.app M) ≫
        ((podCompletedDerivedInverseImage l E g).commShiftIso a).hom.app M.obj ≫
        ((podCompletedToTowerIso l E g M).hom)⟦a⟧' ≫
        ((sfIntegralConstructible l E X).ι.commShiftIso a).inv.app
          ((constructibleIntegralPullback l E g).obj M) := by
  sorry

/-- The canonical shift identification of the tower-defined pullback.
Source: Stacks 08JA (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralPullbackShift (M : sfIntegralConstructibleCategory l E Y) (a : ℤ) :=
  (podIntegralPullbackShift_existsUnique l E g M a).exists.choose

/-- First route of the signed integral Hom shift square.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralShiftRouteLeft
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :=
  (podIntegralHomComparison l E g P)⟦b - a⟧' ≫
    (podIntegralHomShift l E
      ((podPairPullback (constructibleIntegralPullback l E g) _ _
        (podIntegralPairs_pullback l E g)).obj P) a b).hom

/-- Second route, including pullback shifts in both inputs and contravariance.
Source: node proof step 6 (blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
def podIntegralShiftRouteRight
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :=
  (podIntegralPullbackShift l E g ((constructibleIntegralHom l E Y).obj P) (b - a)).inv ≫
    (constructibleIntegralPullback l E g).map (podIntegralHomShift l E P a b).hom ≫
    podIntegralHomComparison l E g (podIntegralShiftPair l E P a b) ≫
    (constructibleIntegralHom l E X).map
      (ObjectProperty.homMk
        (X := (podPairPullback (constructibleIntegralPullback l E g) _ _
          (podIntegralPairs_pullback l E g)).obj (podIntegralShiftPair l E P a b))
        (Y := podIntegralShiftPair l E
          ((podPairPullback (constructibleIntegralPullback l E g) _ _
            (podIntegralPairs_pullback l E g)).obj P) a b)
        (Prod.mkHom (podIntegralPullbackShift l E g P.obj.1.unop a).inv.op
          (podIntegralPullbackShift l E g P.obj.2 b).hom))

/-- The integral square and its actual localized image are equalities of arrows.
The rational equation uses the integral representatives of the cohomological
shifts; the localization CommShift maps identify these with the recorded shifts.
Source: node proof steps 6, 8, 11 and 14.
Proof: apply the fully faithful constructible inclusion to the first equality.
Insert the two normalization equations and cancel the complete-input maps.
The remaining equality is podIntegralReindexedHom_shift. Apply the localization
functor to obtain the second equality. The rational c and its transpose are
exactly these localized maps by podRationalHomComparison_laws, so this is their
shift square, including arbitrary localized arrows by additivity and balancing.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podIntegralRationalHomComparison_shift
    (P : (constructibleIntegralHomPairs l E Y).FullSubcategory) (a b : ℤ) :
    podIntegralShiftRouteLeft l E g P a b = podIntegralShiftRouteRight l E g P a b ∧
    (sfRationalConstructibleLocalization l E X).map (podIntegralShiftRouteLeft l E g P a b) =
      (sfRationalConstructibleLocalization l E X).map
        (podIntegralShiftRouteRight l E g P a b) := by
  sorry
end RestrictedShiftMaps

section CommonShiftImages
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- The common-stage shift square is the class of the rational shift square at
EVERY finite field of definition, followed by the prescribed shift comparisons.
Source: node proof steps 6 and 16.
Proof: represent a permitted pair at its finite coefficient compositum. The
common transpose normalization identifies its c with the rational c there;
common-stage shifts and inclusion CommShift are the prescribed stagewise ones.
Apply the stage inclusion to the rational square. Finite free scalar extension
preserves its evaluation and signed Hom representative formulas, so the same
square results at every larger field. Every common-stage input and arrow has
such a representative, which proves the asserted compatibility on that category.
(blueprint: lem-pod-derived-automorphism-hom-evaluation). -/
theorem podCommonHomComparison_shift
    (F : Index l Ω)
    (P : (constructibleIntegralHomPairs l (Coefficient.{u} l Ω F) Y).FullSubcategory)
    (a b : ℤ) :
    (inclusion F : Stage l Ω X F ⥤ generalAlgebraicallyClosedConstructibleCategory l Ω X).map
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) X).map
          (podIntegralShiftRouteLeft l (Coefficient.{u} l Ω F) g P a b)) =
      (inclusion F : Stage l Ω X F ⥤ generalAlgebraicallyClosedConstructibleCategory l Ω X).map
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) X).map
          (podIntegralShiftRouteRight l (Coefficient.{u} l Ω F) g P a b)) := by
  sorry
end CommonShiftImages

/-- Evaluation-defined natural isomorphisms at all four coefficient stages,
with actual system evaluation and transposition. The signed shift, composition,
completion-unit, reduction and argument-first clauses are the companion
statements in this module, all listed in the owning node's declaration record.
Source: Stacks 0GMX and the agent-formulated derived/completed enhancement in
main-20261015 prop-pod-dual-tate-data-compatibility Steps 1, 2, 4 and 5.
(blueprint: lem-pod-derived-automorphism-hom-evaluation).

Proof, following the node's complete sixteen-step construction:

1. Put $F=g^{-1}$, using the covering-preserving equivalence $(U\to X)\mapsto(U\to X\xrightarrow
gY)$. Its quasi-inverse is inverse image along $g^{-1}$. Thus $F$ is exact, preserves products
and coproducts, and identifies constant finite coefficient sheaves, compatibly with every
quotient map. Also $F\widehat{\mathcal
O}_{E,Y}=F\lim_n(A_{E,n})_Y\cong\lim_n(A_{E,n})_X=\widehat{\mathcal O}_{E,X}$. This is the
actual comparison induced by all the projections. Reindexing sheaves and their module actions
gives mutually inverse module equivalences for these completed ring sheaves as well: the inverse
coefficient map is obtained by the same construction for $g^{-1}$ and their composites are
identities on every projection. The tensor and sheaf-Hom comparisons are those on local
sections, $s\otimes t\mapsto Fs\otimes Ft$ and $f\mapsto Ff$.
Uses: lem-weil-proetale-isomorphism-inverse-image, lem-pur-isomorphism-inverse-image-tensor-hom.

2. These equivalences preserve the resolution classes directly. If $I$ is K-injective and $A$ is
acyclic, a chain map $A\to FI$ corresponds under the inverse exact equivalence to a map
$F^{-1}A\to I$; its null homotopy transports back. If $Q$ is K-flat, then $A\otimes FQ\cong
F(F^{-1}A\otimes Q)$ is acyclic. Flat terms are preserved by the same argument on short exact
sequences. Exactness carries quasi-isomorphisms to quasi-isomorphisms, and termwise application
descends to the derived categories with the specified shift comparison. The termwise unit and
counit still give inverse derived equivalences. At finite coefficients this derived functor is
exactly $P=Lg^*$ in the question.
Uses: def-pur-kinjective-complex, def-pc-kflat-complex,
lem-pur-isomorphism-inverse-image-tensor-hom, lem-weil-pbc-exact-functor-derived-factorization.

3. For finite coefficients, and separately in the ambient completed-ring module category, choose
a representative $K$ of $M$ and a K-injective representative $I$ of $N$. In Hom degree $r$ the
sheaf comparisons of Step 1 give $F\prod_p\mathcal Hom(K^p,I^{p+r})\cong\prod_p\mathcal
Hom(FK^p,FI^{p+r})$. They commute with $d(f)=d_I f-(-1)^r f d_K$, so define an isomorphism of
Hom complexes. Step 2 makes $FI$ an admissible K-injective representative. Consequently
localization gives an isomorphism $c:FH(M,N)\cong H(FM,FN)$. Naturality holds on maps of
complexes, and independence of representatives and descent in both variables follow from the
cited quasi-isomorphism invariance of Hom complexes. In particular this covers arbitrary
unbounded finite-coefficient inputs.
Uses: def-pur-derived-internal-hom, def-pur-hom-complex, lem-pur-rhom-well-defined.

4. The cited internal currying isomorphism, followed by global-Hom recovery, gives the
tensor-Hom transposition bijection. Use flat-term K-flat representatives for the tensor inputs.
The canonical tensor comparison $\mu$ is induced by the ordinary comparison on their total
tensor complexes. Evaluation is ordinary Hom-complex evaluation followed by the inverse
localized augmentation of the target. Reindexing the pure-tensor evaluation $f\otimes x\mapsto
f(x)$ gives the same chain map on either side. When evaluation is written in the order $x\otimes
f$, both sides use the same Koszul symmetry. Thus $\operatorname{ev}_{FM,FN}(1\otimes
c)\mu=F(\operatorname{ev}_{M,N})$. The closed adjunction and its representative normalization
identify this $c$ with the evaluation-defined comparison; the transposition bijection makes it
the unique map satisfying this equation.
Uses: lem-pc-kflat-resolution, lem-weil-pbc-ringed-internal-hom-exact-restriction,
lem-pur-rhom-global-sections, lem-sfb-ringed-derived-monoidal-comparisons,
def-coef-ringed-tensor-hom-model.

5. For $b:M\otimes^L L\to N$ write $b=\operatorname{ev}_{M,N}(1\otimes b^\sharp)$. Apply $F$ and
the naturality of $\mu$. Step 4 gives
$F(b)\mu_{M,L}^{-1}=\operatorname{ev}_{FM,FN}(1\otimes(cF(b^\sharp)))$. Applying the inverse of
the transposition bijection proves the displayed transposition formula. It also proves
naturality in $M,N$: after uncurrying either side of the naturality square one obtains the same
composite of evaluation with the two input maps.
Uses: def-coef-ringed-tensor-hom-model.

6. The shift comparison for $F$ is identity in each degree. The Hom-complex identifications for
$H(M[a],N[b])$ reindex the factors and multiply by the usual signs coming from $d_{K[a]}=(-1)^a
d_K$. Step 3 applies $F$ to the same factors and the same integer signs, so its square with each
of these identifications commutes as a square of complexes. It therefore commutes in the derived
category. This checks shifts in both Hom inputs, rather than only a shift of the output.
Uses: lem-weil-pbc-exact-functor-derived-factorization, def-pur-hom-complex.

7. For a second scheme isomorphism $h:Z\to X$, identify $P_{gh}$ with $P_hP_g$ by the canonical
derived pullback-composition map. The two candidate internal-Hom comparisons become equal after
uncurrying: both give $P_hP_g(\operatorname{ev})$, since the tensor-composition square in the
cited statement commutes. Injectivity of transposition proves the composition identity for $c$.
For the identity scheme map it similarly gives the identity comparison. This is also visible
before localization: two successive reindexings send a local homomorphism $f$ to $h^{-1}g^{-1}f$
in either construction.
Uses: lem-sfb-ringed-derived-monoidal-comparisons, def-coef-ringed-tensor-hom-model.

8. Now work integrally. For a derived-complete input $K$, the canonical quotient-tower unit
$u_K:K\to\mathcal L_Y\mathcal R_YK$ is an isomorphism: apply the finite-free completed-scalar
comparison with $L=E$. In particular this is the canonical unit, not an arbitrarily chosen
isomorphism with a Roos triangle. Reindexing takes each reduction to the corresponding reduction
of $FK$ and commutes with its quotient maps. It commutes with total derived inverse limit: apply
it termwise to a K-injective resolution in the abelian tower category; Step 2's null-homotopy
argument applies to tower maps, and the ordinary limit commutes with this equivalence. Hence
$F\mathcal L_Y\mathcal R_YK\cong\mathcal L_X F_\bullet\mathcal R_YK=Lg^*K$. Composing with
$F(u_K)$ gives the claimed natural identification $FK\cong Lg^*K$, with all its reduction
projections fixed.
Uses: lem-weil-finite-free-completed-scalar-comparison,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-coef-derived-system-evaluation-calculus,
def-weil-derived-pullback-tensor-hom.

9. The same calculation applied to the actual strict tensor-reduction complexes identifies
$F(M\widehat\otimes^L N)$ with $FM\widehat\otimes^L FN$. On a flat-term K-flat model it
reindexes each total-tensor summand, and on the Roos realization it reindexes both product
coordinates and $1-s$. This is the specified completed tensor comparison, since that comparison
is fixed by precisely these representative and Roos-coordinate equations. Coefficient
transitions commute before taking the limit. The comparison is invertible, with inverse given by
inverse reindexing. Substitution of normalized tensor/pullback systems shows that composition,
symmetry, and shift comparisons have the same normalization after realization.
Uses: def-pur-completed-pullback-tensor-comparison,
lem-pur-completed-operation-tower-substitution.

10. To check integral evaluation against completed tensor, use the completion reflector. The
constant-completion comparison identifies quotient-tower completion with Koszul completion,
respecting its unit. The reflector then gives, for a complete target $N$,
$\operatorname{Hom}(\widehat{M\otimes^LL},N)\cong\operatorname{Hom}(M\otimes^LL,N)$
and $\operatorname{Hom}(M\otimes^LL,N)\cong\operatorname{Hom}(L,H(M,N))$.
Here the hat is the functorial completion of the ordinary tensor; its quotient tower is exactly
the defining tower of completed tensor. Thus evaluation for completed tensor is the unique
extension of ordinary evaluation along the completion unit. This establishes transposition on
the complete full subcategory without assuming that ordinary tensor is already complete or that
$M$ is perfect.
Uses: lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-koszul-completion-reflector, def-coef-ringed-tensor-hom-model.

11. Use the ambient completed-ring Hom comparison of Step 3. Under Step 8 it is the required
integral $c$. Its source is constructible by the hypothesis on $H(M,N)$ and preservation of the
integral category by pullback; hence its target is constructible as well. Precompose its
completed evaluation equation with the ordinary-to-completed tensor unit. By Steps 4 and 9 this
becomes the already proved ordinary evaluation equation. The reflector's bijection in Step 10
proves equality of the completed maps. Step 5 now proves the integral transposition formula;
Steps 6 and 7 prove the shift and composition identities, since completion units and both Roos
coordinates commute with reindexing. The hypothesis on the internal Hom is used here to stay on
the stated constructible domain, not to obtain its ambient comparison.
Uses: lem-pur-integral-operations-preserve-constructible,
lem-weil-pbc-ringed-koszul-completion-reflector.

12. For the system assertion, reindex the underlying site while keeping the inverse-sequence
index and all coefficient quotient arrows. This defines an exact equivalence of the two abelian
categories of strict module systems, with an explicit inverse. Step 2 therefore applies to their
unbounded derived categories. On their ringed sequence topoi, the product-Hom-complex
construction of Step 3 gives an actual internal-Hom comparison and Step 4 gives an actual
equality of evaluation maps. For cartesian first inputs its evaluations are the finite-level
comparisons, by the fiberwise-Hom identification in the cited semilinear-system statement. In
the transition formula of that statement, reindexing commutes with scalar extension, $t^M$, its
inverse, $t^N$, and evaluation; consequently it gives the same transpose. Thus the maps respect
the specified system transitions, before evaluation at any level.
Uses: lem-coef-semilinear-derived-sections, lem-coef-derived-system-evaluation-calculus.

13. The comparison with integral reduction is the square having top $\mathcal
R_X(FH(M,N))\to\mathcal R_XH(FM,FN)$ and bottom $F_\bullet\mathcal I_Y(\mathcal R_YM,\mathcal
R_YN)\to\mathcal I_X(\mathcal R_XFM,\mathcal R_XFN)$, with vertical maps the specified $\beta$
and the canonical reduction/reindexing identifications. This square commutes as a system square:
$\beta$ is defined by the same evaluation, and Step 12's reindexing carries that evaluation
chain map and its transpose to themselves. Its unit/counit comparisons are the reduction/limit
adjunction's actual unit and counit, so applying the functorial $\mathcal L$ preserves this
square and all the evaluation and transposition identities. This proves the demanded realization
normalization. It uses neither equality detection by finite evaluations nor invertibility of
$\beta$ for arbitrary inputs; the integral Hom comparison is the ambient one already
constructed.
Uses: lem-coef-derived-system-evaluation-calculus, lem-coef-semilinear-derived-sections.

14. Rationalize the integral maps and their inverses. For arbitrary arrows $a=\sum_i
a_i\otimes\lambda_i$ and $b=\sum_j b_j\otimes\nu_j$ in localized Hom groups, each naturality or
evaluation equation expands by bilinearity to the integral equation for $(a_i,b_j)$ multiplied
by $\lambda_i\nu_j$; similarly the transpose identity is linear in its input. The inverse
identities and shift/composition identities localize as well. This proves the assertion for
arbitrary rational morphisms, rather than just arrows which are integral. These are exactly the
localized operations specified in the question.
Uses: def-weil-rationalization-karoubi, def-weil-derived-pullback-tensor-hom.

15. For a finite coefficient extension $E\subset L$, its completed coefficient sheaf is finite
free over the original completed coefficient sheaf, and ordinary scalar extension agrees
canonically with the specified completed one. The evaluation-normalized derived scalar
adjunction identifies the restriction of $H_S(S\otimes_R^LM,S\otimes_R^LN)$ with
$H_R(M,N\otimes_R^LS)$. On choosing a finite free basis for $S$, the latter is a finite direct
sum of copies of $H_R(M,N)$: internal Hom preserves finite biproducts, either by its Hom-complex
formula or by the transposition bijection. Therefore the scalar comparison is the direct sum of
copies of Step 3's comparison, with evaluation $(f\otimes s)(x\otimes t)=f(x)\otimes st$.
Reindexing fixes the coefficient scalars and hence commutes with this map. This argument uses
finite direct sums only, so imposes no perfectness condition on the inputs. The formula is basis
independent because it is the transpose of evaluation. It commutes with a further extension by
associativity of scalar multiplication and tensor reassociation. The existing operation/scalar
comparisons therefore carry $c$ to the comparison at the larger field, with its evaluation and
shifts.
Uses: lem-weil-finite-free-completed-scalar-comparison,
lem-pur-integral-operations-scalar-extension, lem-sfb-dc-hom-scalar-adjunction.

16. Represent all objects, arrows and the comparisons over one common finite coefficient field
in $\overline{\mathbf Q}_\ell$. Step 15 makes the class of $c$ independent of enlarging that
field. If two arrow representatives become equal at a further field, their naturality equations
and images under $c$ agree there, hence define equal classes. Evaluation, transposition,
inverses, composition and shifts can each be checked at that common field using Steps 11 and 14;
their classes have the required identities. This is precisely the common-stage operation
construction, and completes all coefficient stages.
Uses: def-weil-algebraically-closed-coefficients, def-weil-derived-pullback-tensor-hom.
-/
theorem derivedAutomorphismHomEvaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω] :
    (∃ e : finiteIntrinsicDerivedInternalHom l E Y n ⋙ finiteDerivedPullback l E n g ≅
        ((finiteDerivedPullback l E n g).op.prod (finiteDerivedPullback l E n g)) ⋙
          finiteIntrinsicDerivedInternalHom l E X n,
      ∀ M N, e.hom.app (op M, N) = podFiniteHomComparison l E g n M N) ∧
    (∃ e : constructibleIntegralHom l E Y ⋙ constructibleIntegralPullback l E g ≅
        podPairPullback (constructibleIntegralPullback l E g) _ _
          (podIntegralPairs_pullback l E g) ⋙ constructibleIntegralHom l E X,
      ∀ P, e.hom.app P = podIntegralHomComparison l E g P) ∧
    (∃ e : rationalDerivedInternalHom l E Y ⋙ rationalDerivedPullback l E g ≅
        podPairPullback (rationalDerivedPullback l E g) _ _
          (podRationalPairs_pullback l E g) ⋙ rationalDerivedInternalHom l E X,
      ∀ P, e.hom.app P = podRationalHomComparison l E g P) ∧
    (∃ e : commonStageDerivedInternalHom l Ω Y ⋙ commonStageDerivedPullback l Ω g ≅
        podPairPullback (commonStageDerivedPullback l Ω g) _ _
          (podCommonPairs_pullback l Ω g) ⋙ commonStageDerivedInternalHom l Ω X,
      ∀ P, e.hom.app P = podCommonHomComparison l Ω g P) ∧
    PodPartialHomCompatibility (podIntegralClosed l E Y) (podIntegralClosed l E X)
      (constructibleIntegralPullback l E g) (podIntegralPairs_pullback l E g)
      (canonicalIntegralPullbackTensor l E g) ∧
    PodPartialHomCompatibility (podRationalClosed l E Y) (podRationalClosed l E X)
      (rationalDerivedPullback l E g) (podRationalPairs_pullback l E g)
      (canonicalRationalPullbackTensor l E g) ∧
    PodPartialHomCompatibility (podCommonClosed l Ω Y) (podCommonClosed l Ω X)
      (commonStageDerivedPullback l Ω g) (podCommonPairs_pullback l Ω g)
      (canonicalCommonStagePullbackTensor l Ω g) ∧
    (∀ M N, IsIso (podSystemHomComparison l E g M N)) ∧
    CoefficientEvaluationCompatible (pullbackTensorCalculus l E Y).systemClosed
      (pullbackTensorCalculus l E X).systemClosed (pullbackTensorSequenceDerived l E g)
      (pullbackTensorSystemComparison l E g) := by
  sorry

end WeilConjectures
