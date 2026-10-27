/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W9
-/
module

public import Sheaf.Paper.IntegralOrdinaryPullbackComparison
public import Sheaf.Paper.ConstructibleTensorCompletionChain
public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback

/-! # The tensor/pullback square before inverting completion

Source: fix-prop-projection-formula.proof.md, integral reconstruction;
Stacks 07A4 and 0941. This square involves the forward augmentation maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified signed total tensor, restricted to the flat-term K-flat models.
Source: Stacks 07A4
(blueprint: lem-sf-integral-tensor-pullback-augmentation). -/
@[reducible] def tensorModel (X : Scheme.{u}) :
    ProEtaleTensorModel X ((PurCompactSupport.completed l E).ring X) where
  tensor := ConstructibleTensorModel.ordinaryTensor l E X
  representative := by
    let i : (proEtaleFlatRepresentatives X
        ((PurCompactSupport.completed l E).ring X)).FullSubcategory ⥤
        (integralOperationsGoodComplex l E X).FullSubcategory :=
      ObjectProperty.ιOfLE (fun P hP ↦
        ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1, hP.2⟩)
    with_unfolding_all
      exact Functor.isoWhiskerLeft (i.prod i)
        (ConstructibleTensorModel.tensorRepresentativeIso l E X)

/-- The forward tensor augmentation is fixed on entire flat-term K-flat representatives.
Source: Bhatt--Scholze, Definition 3.4.10; Stacks 0941
(blueprint: lem-sf-integral-tensor-pullback-augmentation). -/
def TensorAugmentationNormalized (X : Scheme.{u})
    (τ : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
    (ConstructibleTensorModel.tensorRepresentativeIso l E X).hom.app (P, Q) ≫
        τ.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (integralCompletedTensorComparison l E X).hom.app (P, Q) =
      DerivedCategory.Q.map
        ((ConstructibleTensorModel.tensorCompletionChain l E X).app (P.obj, Q.obj))

/-- The canonical completed comparison commutes with the forward quotient augmentations.
This is a component equation for specified maps, without constructing any isomorphism
on constructible subcategories and without higher-operation data or properness.

Source: fix-prop-projection-formula.proof.md, integral reconstruction;
Stacks 07A4 and 0941.
(blueprint: lem-sf-integral-tensor-pullback-augmentation).

Proof: resolve both constructible inputs simultaneously by flat-term K-flat complexes.
Replace each tensor augmentation by its defining representative equation and replace
pullComparison by pullIso followed by the normalized ordinary pullback augmentation.
The module adjunction uniqueness defining pullIso preserves the adjunction-unit
sections. At quotient exponent n+1, the two composites send a homogeneous pure tensor
x tensor y to the tensor of the pullbacks of 1 tensor x and 1 tensor y. Balancing,
naturality of the scalar unit and the ordinary tensor-pullback normalization make
these maps equal; the quotient transition equations give equality of entire strict
towers. The maps from total tensor to each strict Roos cone have those same product
components and zero shifted component. Product and mapping-cocone extensionality
therefore prove equality of chain maps. The definition of the canonical completed
comparison is the derived-limit image of this coherent tensor comparison, conjugated
by the specified reduction/limit counits. Substitute those counits and cancel their
inverse pairs by the adjunction triangle identities. Faithful whiskering by the
product of the good-complex localizations descends the representative equality to
the displayed derived equality. This applies also to zero inputs and empty schemes;
no inference of equality from individual derived evaluations is used. -/
theorem tensorPullback_augmentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (τX : (tensorModel l E X).tensor ⟶ integralCompletedTensor l E X)
    (τY : (tensorModel l E Y).tensor ⟶ integralCompletedTensor l E Y)
    (hX : TensorAugmentationNormalized l E X τX)
    (hY : TensorAugmentationNormalized l E Y τY)
    (M N : sfIntegralConstructibleCategory l E Y) :
    (PurCompactSupport.pull (PurCompactSupport.completed l E) f).map
        (τY.app (M.obj, N.obj)) ≫
      (pullComparison l E f).app ((integralCompletedTensor l E Y).obj (M.obj, N.obj)) ≫
      ((canonicalIntegralPullbackTensor l E f M N).hom).hom =
    (proEtaleCanonicalTensorComparison f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f)
        (tensorModel l E Y) (tensorModel l E X)).hom.app (M.obj, N.obj) ≫
      τX.app
        ((PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj M.obj,
          (PurCompactSupport.pull (PurCompactSupport.completed l E) f).obj N.obj) ≫
      (integralCompletedTensor l E X).map
        (Prod.mkHom ((pullComparison l E f).app M.obj)
          ((pullComparison l E f).app N.obj)) := by sorry

end WeilConjectures.IntegralOrdinary
