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
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison
import all Sheaf.Paper.ScalarRoosComparison
import Sheaf.Paper.CompletedTensorSectionProperties

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
set_option backward.isDefEq.respectTransparency.types false
open scoped ChangeOfRings
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

section AugmentationProof
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
attribute [local implicit_reducible] integralOperationsRoosFunctor
  integralOperationsRoos scalarPullbackRoosEnd completedOrdinaryScalarComplex
  scalarPullbackSourceTower scalarPullbackTargetTower
attribute [local irreducible] completedScalarChangeData
attribute [local implicit_reducible] completedOrdinaryScalarExtension
attribute [local irreducible]
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  integralScalarReductionWitness integralScalarReduction integralScalarTensorSection
  unrestrictedIntegralReductionExistence unrestrictedIntegralReductionFunctor
  unrestrictedIntegralTensorSection inverseImageCompletedCoefficientMap

private theorem completedTensor_smul (W : AlgebraicGeometry.Scheme.{u})
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ)
    (a : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U)
    (x : M.val.obj U) :
    completedScalarTensorSection l E L ι W M U a x =
      a • completedScalarTensorSection l E L ι W M U 1 x := by
  exact (completedTensorSectionProperties l E L ι W M).1 U a x

private theorem completedTensor_restrict (W : AlgebraicGeometry.Scheme.{u})
    (M : integralTowerModules l E W) {U V : W.ProEtᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) :
    (((completedOrdinaryScalarExtension l E L ι W).obj M).val.map f)
        (completedScalarTensorSection l E L ι W M U 1 x) =
      completedScalarTensorSection l E L ι W M V 1 (M.val.map f x) := by
  exact (completedTensorSectionProperties l E L ι W M).2 f x

private theorem augmentation_first
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l F Y) ℤ) (n : ℕ) (i : ℤ) :
    (inverseImageRoosComparisonComplex l F g P).f i ≫
        (CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l F X
          ((integralOperationsPullbackTowerFunctor l F g).obj P))).f i ≫
        (Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l F g).obj P).obj
          (op m)) n).f i =
      (inverseImageReductionTheta l F g n P).f i := by
  simp only [inverseImageRoosComparisonComplex, scalarPullbackRoosEnd,
    integralOperationsPullbackTowerFunctor,
    Functor.flip_obj_obj, ← Category.assoc,
    CochainComplex.mappingCocone.lift_f_fst_f]
  change (inverseImageReductionProduct l F g P ≫ Pi.π _ n).f i = _
  simp only [inverseImageReductionProduct, Pi.lift_π]

private theorem augmentation_second
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : CochainComplex (integralTowerModules l F Y) ℤ) (i : ℤ) :
    (inverseImageRoosComparisonComplex l F g P).f i ≫
        (CochainComplex.mappingCocone.snd (scalarPullbackRoosEnd l F X
          ((integralOperationsPullbackTowerFunctor l F g).obj P))).v
            i (i - 1) (by omega) = 0 := by
  simp only [inverseImageRoosComparisonComplex, scalarPullbackRoosEnd,
    integralOperationsPullbackTowerFunctor,
    Functor.flip_obj_obj, CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v]

private theorem finite_square
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : ScalarPullbackStrictConeData l E L ι g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) (n : ℕ) :
    (completedOrdinaryScalarComplex l E L ι X).map
        (inverseImageReductionTheta l E g n P.obj) ≫ (D.level.app P.obj).app (op n) =
      b.hom.app P ≫ inverseImageReductionTheta l L g n
        ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply completedScalar_tensor_ext l E L ι X
    ((inverseImageIntegralModules l E g).obj (P.obj.X i))
  intro U a x
  let M := (inverseImageIntegralModules l E g).obj (P.obj.X i)
  let f := ((completedOrdinaryScalarComplex l E L ι X).map
    (inverseImageReductionTheta l E g n P.obj) ≫ (D.level.app P.obj).app (op n)).f i
  let h := (b.hom.app P ≫ inverseImageReductionTheta l L g n
    ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).f i
  change f.val.app U (completedScalarTensorSection l E L ι X M U a x) =
    h.val.app U (completedScalarTensorSection l E L ι X M U a x)
  suffices hf : f.val.app U (completedScalarTensorSection l E L ι X M U 1 x) =
      h.val.app U (completedScalarTensorSection l E L ι X M U 1 x) by
    rw [completedTensor_smul]
    simpa only [map_smul] using congrArg (fun z ↦ a • z) hf
  let V := (proEtaleIsoPostcompose g).obj U.unop
  let q := (proEtaleIsoCommaArrow g U.unop).op
  have hθ := (inverseImageReductionTheta_existsUnique l E g n P.obj).exists.choose_spec
    i U.unop x
  have hbb := hb P i U.unop 1 x
  simp only [map_one] at hbb
  have hθ' := (inverseImageReductionTheta_existsUnique l L g n
    ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).exists.choose_spec
    i U.unop (completedScalarTensorSection l E L ι Y (P.obj.X i) (op V) 1 x)
  change (((D.level.app P.obj).app (op n)).f i).val.app U
      (((completedOrdinaryScalarExtension l E L ι X).map
        ((inverseImageReductionTheta l E g n P.obj).f i)).val.app U
          (completedScalarTensorSection l E L ι X M U 1 x)) =
    ((inverseImageReductionTheta l L g n
      ((completedOrdinaryScalarComplex l E L ι Y).obj P.obj)).f i).val.app U
        (((b.hom.app P).f i).val.app U
          (completedScalarTensorSection l E L ι X M U 1 x))
  erw [completedScalarTensorSection_naturality, hθ, hbb, hθ']
  erw [← completedTensor_restrict]
  have hn := PresheafOfModules.naturality_apply
    (((D.level.app P.obj).app (op n)).f i).val q
      (completedScalarTensorSection l E L ι X
        (((integralOperationsPullbackLevel l E g n).obj P.obj).X i)
        (op ((proEtaleBaseChange g).obj V)) 1
        (integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) V
          (unrestrictedIntegralTensorSection l E Y n (P.obj.X i) (op V) 1 x)))
  erw [hn]
  congr 1
  simpa only [scalarPullbackGenerator, map_one, one_smul, one_mul, mul_one, id_eq] using
    D.generator P.obj n i V x 1 1 1

private theorem cone_first
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (D : ScalarPullbackStrictConeData l E L ι g)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (n : ℕ) :
    ((scalarPullbackConeMap l E L ι g D.level D.cone).app P).f i ≫
        (CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l L X
          ((scalarPullbackTargetTower l E L ι g).obj P))).f i ≫
        (Pi.π (fun m ↦ ((scalarPullbackTargetTower l E L ι g).obj P).obj (op m)) n).f i =
      (completedOrdinaryScalarExtension l E L ι X).map
        ((CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l E X
          ((integralOperationsPullbackTowerFunctor l E g).obj P))).f i ≫
        (Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
          (op m)) n).f i) ≫ ((D.level.app P).app (op n)).f i := by
  have hr := congrArg (fun a ↦ a.f i) (scalarRoosTowerCoordinates (D.level.app P)).1
  dsimp only [HomologicalComplex.comp_f] at hr
  have hp := congrArg (fun a ↦ a.f i)
    (Pi.map_π (fun m ↦ (D.level.app P).app (op m)) n)
  simp only [HomologicalComplex.comp_f] at hp
  have hk := (D.coordinates P i).1
  have hπ : (scalarPullbackProductMap l E L ι X
      (fun m ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op m))).f i ≫
        (Pi.π (fun m ↦ ((scalarPullbackSourceTower l E L ι g).obj P).obj (op m)) n).f i =
      (completedOrdinaryScalarExtension l E L ι X).map
        ((Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
          (op m)) n).f i) := by
    unfold scalarPullbackProductMap
    change (Pi.lift (fun m ↦ (completedOrdinaryScalarComplex l E L ι X).map
      (Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
        (op m)) m)) ≫ Pi.π (fun m ↦ (completedOrdinaryScalarComplex l E L ι X).obj
          (((integralOperationsPullbackTowerFunctor l E g).obj P).obj (op m))) n).f i = _
    rw [Pi.lift_π]
    rfl
  dsimp only [scalarPullbackRoosEnd] at *
  change ((D.cone.hom.app P).f i ≫
    (integralOperationsRoosMap (D.level.app P)).f i) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  have hr' := congrArg ((D.cone.hom.app P).f i ≫ ·) hr
  have hr'' := congrArg (· ≫ (Pi.π
    (fun m ↦ ((scalarPullbackTargetTower l E L ι g).obj P).obj (op m)) n).f i) hr'
  simp only [Category.assoc] at hr''
  refine hr''.trans ?_
  have hp' := congrArg ((D.cone.hom.app P).f i ≫
    (CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l L X
      ((scalarPullbackSourceTower l E L ι g).obj P))).f i ≫ ·) hp
  refine hp'.trans ?_
  have hk' := congrArg (· ≫ (Pi.π
    (fun m ↦ ((scalarPullbackSourceTower l E L ι g).obj P).obj (op m)) n).f i ≫
      ((D.level.app P).app (op n)).f i) hk
  simp only [Category.assoc] at hk'
  refine hk'.trans ?_
  have hπ' := congrArg ((completedOrdinaryScalarExtension l E L ι X).map
    ((CochainComplex.mappingCocone.fst (scalarPullbackRoosEnd l E X
      ((integralOperationsPullbackTowerFunctor l E g).obj P))).f i) ≫ · ≫
        ((D.level.app P).app (op n)).f i) hπ
  simpa only [scalarPullbackRoosEnd, Category.assoc, Functor.map_comp] using hπ'

private theorem cone_second
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (D : ScalarPullbackStrictConeData l E L ι g)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) :
    ((scalarPullbackConeMap l E L ι g D.level D.cone).app P).f i ≫
        (CochainComplex.mappingCocone.snd (scalarPullbackRoosEnd l L X
          ((scalarPullbackTargetTower l E L ι g).obj P))).v i (i - 1) (by omega) =
      (completedOrdinaryScalarExtension l E L ι X).map
        ((CochainComplex.mappingCocone.snd (scalarPullbackRoosEnd l E X
          ((integralOperationsPullbackTowerFunctor l E g).obj P))).v
            i (i - 1) (by omega)) ≫
        (scalarPullbackProductMap l E L ι X
          (fun m ↦ ((integralOperationsPullbackTowerFunctor l E g).obj P).obj
            (op m))).f (i - 1) ≫
        (Limits.Pi.map (fun m ↦ (D.level.app P).app (op m))).f (i - 1) := by
  have hr := (scalarRoosTowerCoordinates (D.level.app P)).2 i (i - 1) (by omega)
  dsimp only [scalarPullbackRoosEnd] at *
  change ((D.cone.hom.app P).f i ≫
    (integralOperationsRoosMap (D.level.app P)).f i) ≫ _ = _
  have hr' := congrArg ((D.cone.hom.app P).f i ≫ ·) hr
  simpa only [Category.assoc] using hr'.trans (by
    rw [← Category.assoc]
    exact congrArg (· ≫ (Limits.Pi.map
      (fun m ↦ (D.level.app P).app (op m))).f (i - 1)) (D.coordinates P i).2)

private theorem right_coordinate
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (hb : CompletedFormula l E L ι g b) :
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
  let Q := (completedOrdinaryScalarComplex l E L ι Y).obj P.obj
  let c := b.hom.app P ≫ inverseImageRoosComparisonComplex l L g Q
  intro i n U s0 p
  have hf := augmentation_first l L g Q n i
  have hb1 := hb P i U 1 p
  simp only [map_one] at hb1
  have hc : c.f i ≫ (CochainComplex.mappingCocone.fst
        (scalarPullbackRoosEnd l L X
          ((integralOperationsPullbackTowerFunctor l L g).obj Q))).f i ≫
        (Pi.π (fun m ↦ ((integralOperationsPullbackTowerFunctor l L g).obj Q).obj
          (op m)) n).f i =
      (b.hom.app P).f i ≫ (inverseImageReductionTheta l L g n Q).f i := by
    simpa only [c, HomologicalComplex.comp_f, Category.assoc] using
      congrArg ((b.hom.app P).f i ≫ ·) hf
  change ((c.f i ≫ _ ≫ _).val.app (op U)) _ = _
  have hh := congrArg (fun k ↦ k.val.app (op U)) hc
  refine (congrArg (fun k ↦ k
    (completedScalarTensorSection l E L ι X
      ((inverseImageIntegralModules l E g).obj (P.obj.X i)) (op U)
      ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s0) p)) hh).trans ?_
  rw [completedTensor_smul l E L ι X
    ((inverseImageIntegralModules l E g).obj (P.obj.X i)) (op U)
    ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s0) p]
  change ((inverseImageReductionTheta l L g n Q).f i).val.app (op U)
    (((b.hom.app P).f i).val.app (op U) (_ • _)) = _
  rw [map_smul, map_smul]
  exact congrArg (fun z ↦ ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) s0) •
    (((inverseImageReductionTheta l L g n Q).f i).val.app (op U) z)) hb1


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
  let D := specifiedPullbackConeData l E L ι g hX hY
  let Q := (completedOrdinaryScalarComplex l E L ι Y).obj P.obj
  let a := (completedOrdinaryScalarComplex l E L ι X).map
    (inverseImageRoosComparisonComplex l E g P.obj)
  let δ := (scalarPullbackConeMap l E L ι g D.level D.cone).app P.obj
  let c := b.hom.app P ≫ inverseImageRoosComparisonComplex l L g Q
  have hs (i : ℤ) : c.f i ≫ (CochainComplex.mappingCocone.snd
      (scalarPullbackRoosEnd l L X
        ((integralOperationsPullbackTowerFunctor l L g).obj Q))).v
          i (i - 1) (by omega) = 0 := by
    dsimp only [c, HomologicalComplex.comp_f]
    rw [Category.assoc, augmentation_second, comp_zero]
  refine ⟨?_, hs, ?_⟩
  · change a ≫ δ = c
    apply HomologicalComplex.Hom.ext
    funext i
    apply cocone_degree_ext _ (a ≫ δ) c i
    · apply complexProduct_hom_ext
      intro n
      have hf := congrArg (fun z ↦ z.f i) (finite_square l E L ι g D P b _hb n)
      simp only [HomologicalComplex.comp_f] at hf
      dsimp only [HomologicalComplex.comp_f]
      simp only [Category.assoc]
      erw [cone_first l E L ι g D P.obj i n]
      change (completedOrdinaryScalarExtension l E L ι X).map
        ((inverseImageRoosComparisonComplex l E g P.obj).f i) ≫ _ = _
      rw [← Category.assoc, ← Functor.map_comp, augmentation_first]
      change (completedOrdinaryScalarExtension l E L ι X).map
        ((inverseImageReductionTheta l E g n P.obj).f i) ≫ _ = _ at hf
      rw [hf]
      dsimp only [c, HomologicalComplex.comp_f]
      simp only [Category.assoc]
      exact congrArg ((b.hom.app P).f i ≫ ·)
        (augmentation_first l L g Q n i).symm
    · dsimp only [HomologicalComplex.comp_f]
      simp only [Category.assoc]
      erw [cone_second l E L ι g D P.obj i]
      rw [← Category.assoc]
      change ((completedOrdinaryScalarExtension l E L ι X).map
        ((inverseImageRoosComparisonComplex l E g P.obj).f i) ≫
          (completedOrdinaryScalarExtension l E L ι X).map _) ≫ _ = _
      rw [← Functor.map_comp, augmentation_second]
      simp only [Functor.map_zero, zero_comp]
      simpa only [scalarPullbackRoosEnd] using (hs i).symm
  · exact right_coordinate l E L ι g P b _hb

end AugmentationProof

end AlgebraicGeometry.ProEtale.IsomorphismScalarTensor
