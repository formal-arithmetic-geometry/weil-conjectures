/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.IsomorphismScalarTensorKFlatModel
public import Sheaf.Paper.SpecifiedPullbackComparisonAlpha
public import Sheaf.Paper.ScalarPullbackStrictConeNaturality
public import Sheaf.Paper.SfIntegralConstructible

/-! # Strict scalar compatibility of the specified quotient-cone augmentation

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50–51, for completed
pullback; the strict coefficient identity is the node's agent calculation
(blueprint: lem-weil-isomorphism-scalar-augmentation-cone).

The natural isomorphism b is the predecessor's completed tensor comparison,
specified by its local formula. No localization is used in the conclusion.
Index n denotes positive exponent n+1. The mapping-cocone first projection is the
unshifted product, and its second projection is the shifted product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures
namespace WeilConjectures


/-- The unique normalized strict tower, tensor/product comparison and derived descent.
The generator and both cone-coordinate equations are fields of this existing type.
Source: Stacks 03EK, 08TC; Bhatt--Scholze 6.5.9(4), agent quotient-cone calculation
(blueprint: lem-weil-isomorphism-scalar-augmentation-cone). -/
def specifiedPullbackConeData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :
    ScalarPullbackStrictConeData l E L ι g :=
  Classical.choice (scalarPullbackStrictConeNaturality l E L ι g hX hY).2.2.2.1

/-- The specified whole-cone delta in the shared universal ordinary tensor model.
It is diagonal on the two product coordinates, with the prescribed finite-level maps.
Source: Stacks 03EK, 08TC; Bhatt--Scholze 6.5.9(4), agent quotient-cone calculation
(blueprint: lem-weil-isomorphism-scalar-augmentation-cone). -/
def specifiedPullbackConeChain
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y)) :=
  scalarPullbackConeMap l E L ι g
    (specifiedPullbackConeData l E L ι g hX hY).level
    (specifiedPullbackConeData l E L ι g hX hY).cone


end WeilConjectures

namespace AlgebraicGeometry.ProEtale.IsomorphismScalarTensor

/-- The augmentation square commutes strictly, with zero shifted component and the
specified common finite quotient coordinates. The binder b and CompletedFormula
select exactly the tensor comparison of the predecessor, rather than an arbitrary
isomorphism. The representative P is K-flat with flat terms; e identifies it with K.
In the last equation the completed scalar acts through pi_L,n on the restricted
finite pullback, so its right side is (g^-1(p tensor 1)) tensor pi_L,n(s).

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4), pp. 50–51 (context only);
agent calculation using Stacks 03EK, 03D6 and 08TC
(blueprint: lem-weil-isomorphism-scalar-augmentation-cone).

Proof:
1. By lem-weil-proetale-isomorphism-inverse-image, inverse image is sectionwise
   on the isomorphic site. Write y=g^-1(p), s=c_L(g^-1(s0)). Pure tensors generate
   the sheafified tensor locally (def-pur-sheaf-tensor-product), so these suffice.
2. The augmentation of def-weil-inverse-image-pullback-comparison has zero shifted
   coordinate. Tensor preserves zero, and delta applies the level maps separately
   to the two cone coordinates (lem-weil-specified-pullback-comparison-alpha).
   The right composite also has zero shifted coordinate.
3. In the left composite substitute a=b=1 in the specified level formula of
   lem-weil-specified-pullback-comparison-alpha. Preservation of 1 gives exactly
   (g^-1(p tensor 1)) tensor pi_L,n(s) in its unshifted quotient coordinate.
4. By lem-weil-isomorphism-scalar-tensor-kflat-model the right composite first gives
   g^-1(p tensor s0). Its augmentation gives g^-1((p tensor s0) tensor 1) tensor 1.
   Tensor balancing identifies this with g^-1(p tensor pi_Y(s0)) tensor 1, then
   with g^-1(p tensor 1) tensor c_A(g^-1(pi_Y(s0))). The defining projection
   equation pi_X c_L = c_A g^-1(pi_Y) of
   def-weil-inverse-image-pullback-comparison makes this the coordinate in step 3.
5. Additivity and sheafification extend equality from local pure tensors to all
   sections. Product extensionality and the two cone projections give equality
   in every degree, hence equality of chain maps (def-weil-abstract-derived-category).
   This is an equality before passage to quasi-isomorphism localization.
-/
theorem isomorphism_scalar_augmentation_cone
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.residueField x))
    (hY : ∀ y : Y, IsUnit (l : Y.residueField y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (_hK : sfIntegralConstructible l E Y K)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (_e : DerivedCategory.Q.obj P.obj ≅ K)
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (_hb : CompletedFormula l E L ι g b) :
    (completedOrdinaryScalarComplex l E L ι X).map
        (inverseImageRoosComparisonComplex l E g P.obj) ≫
        (specifiedPullbackConeChain l E L ι g hX hY).app P.obj =
      b.hom.app P ≫ inverseImageRoosComparisonComplex l L g
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) ∧
    (∀ i : ℤ,
      ((b.hom.app P ≫ inverseImageRoosComparisonComplex l L g
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).f i) ≫
        (CochainComplex.mappingCocone.snd (scalarPullbackRoosEnd l L X
          ((integralOperationsPullbackTowerFunctor l L g).obj
            ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)))).v
              i (i - 1) (by omega) = 0) ∧
    ∀ (i : ℤ) (n : ℕ) (U : X.ProEt)
      (s0 : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
        (op ((proEtaleIsoPostcompose g).obj U)))
      (p : (P.obj.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))),
      (((b.hom.app P ≫ inverseImageRoosComparisonComplex l L g
          ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).f i ≫
        (CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l L X
          ((integralOperationsPullbackTowerFunctor l L g).obj
            ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)))).f i ≫
        (Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l L g).obj
          ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).obj (op m)) n).f i).val.app
            (op U))
        (completedScalarTensorSection l E L ι X
          (((inverseComplex l E g).obj P.obj).X i) (op U)
          ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s0) p) =
      ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s0) •
        (((inverseImageReductionTheta l L g n
          ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).f i).val.app (op U)
          (completedScalarTensorSection l E L ι Y (P.obj.X i)
            (op ((proEtaleIsoPostcompose g).obj U)) 1 p)) := by
  sorry

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
