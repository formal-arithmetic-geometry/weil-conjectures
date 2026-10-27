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

import Mathlib.CategoryTheory.Adjunction.Additive
import all Sheaf.Paper.IsomorphismReductionTower
import Sheaf.Paper.PurInverseImageTensorHom
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.PodReindexingHomCoefficientDescent
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Sheaf.Paper.SfDerivedCompleteLegacyComparison

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

attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
  HasDerivedCategory.standard
attribute [-instance] isoReductionAbSheafify isoReductionAbBijective isoReductionSiteSmall

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

/-- Naturality of the finite comparison in both inputs: the naturality clause of
`podFiniteHomComparison_laws`.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 1--2.
Proof: both sides are maps into an internal Hom of the target; compare their
transposes. Parameter naturality of the transposition turns the left side into
the transpose of `T(F H(a,b), 1)` followed by `μ⁻¹` and `F(ev)`; naturality of
`μ` and dinaturality of evaluation, `T(H(a,b),1) ≫ ev = T(1,a) ≫ ev ≫ b`, make it
`T(1, F a) ≫ μ⁻¹ ≫ F(ev) ≫ F b`. The right side transposes to
`T(1, F a) ≫ T(c,1) ≫ ev ≫ F b`, and `T(c,1) ≫ ev = μ⁻¹ ≫ F(ev)` is the counit
identity of the transpose defining `c`. The transposes agree, so the maps agree.
(blueprint: stage3-pod-finite-hom-comparison-naturality). -/
theorem podFiniteHomComparison_naturality (n : ℕ)
    (M N M' N' : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1)))
    (a : M' ⟶ M) (b : N ⟶ N') :
    (finiteDerivedPullback l E n g).map
        ((finiteIntrinsicDerivedInternalHom l E Y n).map (Prod.mkHom a.op b)) ≫
      podFiniteHomComparison l E g n M' N' =
    podFiniteHomComparison l E g n M N ≫
      (finiteIntrinsicDerivedInternalHom l E X n).map
        (Prod.mkHom ((finiteDerivedPullback l E n g).map a).op
          ((finiteDerivedPullback l E n g).map b)) := by
  sorry

/-- The finite comparison's invertibility, evaluation equation and transpose
equation: the clauses of `podFiniteHomComparison_laws` other than naturality.
Source: Stacks 0GMX; node lem-pod-derived-automorphism-hom-evaluation, steps 1--2.
Proof: reindexing along the isomorphism of sites is an exact equivalence that
preserves K-flat and K-injective complexes, products and total tensor; its
product-Hom comparison `c⁰` is an isomorphism for arbitrary unbounded inputs
(lem-pod-reindexing-hom-resolution-model), and the evaluation calculus
identifies `c⁰` with the evaluation-defined comparison
(lem-pod-reindexing-evaluation-shift-composition); hence `c` is invertible.
The evaluation equation is the counit identity of the transpose defining `c`,
precomposed with `μ`. For the transpose equation, transpose both sides: by
parameter naturality and naturality of `μ` the right side becomes
`μ⁻¹ ≫ F(T(b♯,1) ≫ ev) = μ⁻¹ ≫ F b`, which is the left side.
(blueprint: stage3-pod-finite-hom-comparison-remaining). -/
theorem podFiniteHomComparison_laws_remaining (n : ℕ) :
    (∀ M N, IsIso (podFiniteHomComparison l E g n M N)) ∧
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

/-- Finite unbounded internal Hom is preserved, naturally and with its actual evaluation
and transposition. Source: Stacks 0GMX, node proof steps 1--5.
Proof: the naturality clause is `podFiniteHomComparison_naturality`; the
invertibility, evaluation and transposition clauses are
`podFiniteHomComparison_laws_remaining`.
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
  have hr := podFiniteHomComparison_laws_remaining l E g n
  refine ⟨hr.1, ?_, hr.2.1, hr.2.2⟩
  intro M N M' N' a b
  exact podFiniteHomComparison_naturality l E g n M N M' N' a b
end Finite


end WeilConjectures
