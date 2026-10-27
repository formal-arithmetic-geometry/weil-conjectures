/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteRestrictionCoefficientGeometry
/-!
# Normalization of finite restriction comparisons

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; the finite-stalk
step of the blueprint finite pushforward proof (blueprint: def-zl-finite-restriction-normalization).

## Main definitions

- `WeilConjectures.FiniteRestrictionCoefficient.Endpoints.ScalarNormalized`: normalization of
finite restriction comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FiniteRestrictionCoefficient
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage integralTransition transition stageSystem)
variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω] {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
attribute [local irreducible] IntegralDiagram.functor PullbackDiagram.functor
  sfIntegralConstructible sfConstructibleIntegralScalarExtension HasDerivedCategory.standard
/-- Projection-normalized agreement of ordinary completed direct image with every
Roos presentation of the prescribed reduction-tower image.
Source: Stacks 0D6E, 0A07; Bhatt--Scholze 6.8.15
(blueprint: def-zl-finite-restriction-normalization). -/
def TowerAgreement {Z V : Scheme.{u}} (a : Z ⟶ V) : Prop :=
  ∀ (A : Index l Ω) (K : IntegralStage l Ω Z A)
    [HasProduct (sfDirectImageTerm l (Coefficient.{u} l Ω A) a K.obj)]
    (M : SfIntegralDirectImage l (Coefficient.{u} l Ω A) a K.obj),
    ∃ e : (sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω A) a).obj K.obj ≅ M.obj,
      ∀ n : ℕ, e.hom ≫ M.projection ≫ Pi.π _ n =
        (sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω A) a).map
          ((sfDerivedReductionUnit l (Coefficient.{u} l Ω A) Z n).app K.obj) ≫
        (sfDerivedRestrictionComparison l (Coefficient.{u} l Ω A) a n).hom.app
          ((scalarReductionDerivedExtension l (Coefficient.{u} l Ω A) Z n).obj K.obj)

/-- The endpoint comparisons commute with the normalized geometric scalar maps.
These equations fix the scalar comparisons on the three actual functors.
Source: Bhatt--Scholze 6.8.14; Stacks 0959, 03QP, 099N
(blueprint: def-zl-finite-restriction-normalization). -/
def Endpoints.ScalarNormalized {G : Geometry l Ω f y} {I : IntegralComparisons l f y Ω}
    (N : Endpoints l Ω f y G I) : Prop :=
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω X A),
    (I.beta .source A B h).hom.app K ≫
        (N.source B).hom.app ((integralTransition l Ω X A B h).obj K) =
      (integralTransition l Ω s A B h).map ((N.source A).hom.app K) ≫
        (G.pointPull.beta A B h).hom.app ((G.image.integral A).image.obj K) ≫
        (G.pointPull.integral.functor B).map ((G.image.integralComparison A B h).inv.app K)) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω X A),
    (I.beta .middle A B h).hom.app K ≫
        (N.middle B).hom.app ((integralTransition l Ω X A B h).obj K) =
      (integralTransition l Ω s A B h).map ((N.middle A).hom.app K) ≫
        (G.fibreImage.integralComparison A B h).inv.app
          ((G.fibrePull.integral.functor A).obj K) ≫
        (G.fibreImage.integral B).image.map ((G.fibrePull.beta A B h).hom.app K)) ∧
  (∀ (A B : Index l Ω) (h : A ≤ B) (K : IntegralStage l Ω X A)
    (x : FiniteCounitTowers.Points f y),
    (I.beta .target A B h).hom.app K ≫
        (N.projection B x).app ((integralTransition l Ω X A B h).obj K) =
      (integralTransition l Ω s A B h).map ((N.projection A x).app K) ≫
        ((G.pointComponent x).beta A B h).hom.app K)

/-- The literal tensor-generator formula for each specified strict counit component.
Together with the normalized scalar squares this fixes the finite-level germ formula.
Source: Stacks 03QP, 06YY; Bhatt--Scholze 6.8.14
(blueprint: def-zl-finite-restriction-normalization). -/
def TensorRestrictionFormula : Prop :=
  ∀ (A B : Index l Ω) (h : A ≤ B) (x : FiniteCounitTowers.Points f y)
    (M : coefficientSequenceModules l (Coefficient.{u} l Ω A) X)
    (U : (ℕ × s.ProEt)ᵒᵖ)
    (a : (coefficientSequenceCommRingSheaf l (Coefficient.{u} l Ω B) s).obj.obj U)
    (m : ((FiniteCounitTowers.pull l (Coefficient.{u} l Ω A) (pullback.fst f y) ⋙
      FiniteCounitTowers.push l (Coefficient.{u} l Ω A) (pullback.snd f y)).obj M).val.obj U),
    (((integralComparisonSequenceScalarModel l (Coefficient.{u} l Ω A)
      (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h) s).E.map
        ((FiniteCounitTowers.component l (Coefficient.{u} l Ω A) f y x).app M)).val.app U)
      (integralComparisonSequenceTensorSection l (Coefficient.{u} l Ω A)
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h) s _ U a m) =
      integralComparisonSequenceTensorSection l (Coefficient.{u} l Ω A)
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h) s _ U a
        (((FiniteCounitTowers.component l (Coefficient.{u} l Ω A) f y x).app M).val.app U m)

end WeilConjectures.FiniteRestrictionCoefficient
