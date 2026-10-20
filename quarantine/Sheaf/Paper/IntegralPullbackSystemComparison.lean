/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.NormalizedDVREffectivity

/-! # Integral pullback and coherent finite-system reduction

Source: Stacks Project, Tags 099N(5) and 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical reduction rho of integral pullback, computed using any good resolution.
The first factor is the actual projection-adjoint map, whose invertibility is precisely
part (1) of integralOperations_preserve_constructible. The other factors only change
finite pullback presentation and identify the reduction of the representative with
that of K through the universal reduction counit.
Source: Stacks Tag 099N(5); Bhatt--Scholze, Lemma 6.5.9(5)
(blueprint: lem-pod-integral-pullback-system-comparison). -/
def integralSystemPullbackReductionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (K : sfIntegralConstructibleCategory l E Y)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (e : (DerivedCategory.Q (C := scalarReductionSource l E Y)).obj P.obj ≅ K.obj) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((constructibleIntegralPullback l E f).obj K).obj ≅
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).obj
        ((scalarReductionDerivedExtension l E Y n).obj K.obj) :=
  letI := ((integralOperations_preserve_constructible l E f).1 K.obj K.property).2 P e n
  asIso (integralPullbackFiniteComparison l E f K.obj P e n) ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
        (ComplexShape.up ℤ)).app ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)) ≪≫
    ((proEtaleConstantRingPullback
      (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.app
        ((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj)).symm ≪≫
    (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f).mapIso
      ((coefficientFiniteReductionModel l E Y P.obj P.property.1 n).symm ≪≫
        (scalarReductionDerivedExtension l E Y n).mapIso e)

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralSystemPullbackReductionIso
  constructibleIntegralPullback integralDerivedPullback
  integralSystemReduction integralSystemReductionEvaluation
  finiteSystemDerivedPullback finiteSystemDerivedEvaluation
  finiteSystemDerivedPullbackEvaluation

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Integral pullback reduces to exact inverse image on coherent finite systems.
The evaluated comparison is the adjoint of the actual Roos projection, for every
flat-term K-flat representative. No composition comparison is asserted here.
Source: Stacks 099N(5), 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).

Proof: reduce one flat-term K-flat representative with the strict quotient maps.
Change of rings preserves its K-flatness; quotient tensor reassociation and finite
inverse image preserve normalization. The strict Roos comparison, natural on chain
maps and their localization, identifies the actual integral pullback with total
limit of this pulled-back reduction system, preserving its projections. Apply the
reduction/total-limit adjunction counit to this identification. Normalized DVR
effectivity makes its evaluations invertible; the evaluation criterion in the
coefficient calculus makes the system map invertible. Naturality of the adjunction
and Roos comparison gives a natural system isomorphism. The counit projection
formula identifies its evaluation with the scalar adjoint of the defining tower
projection. Transport through the unit-normalized finite pullback presentation
and the universal reduction counit gives exactly the displayed formula, for every
representative and every positive uniformizer exponent. -/
theorem integralPullbackSystemComparison :
    ∃ β : ∀ {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y),
        constructibleIntegralPullback l E f ⋙ integralSystemReduction l E X ≅
          integralSystemReduction l E Y ⋙
            finiteSystemDerivedPullback (integralSystemRings l E) (integralSystemTransition l E) f,
      ∀ {X Y : Scheme.{u}}
        [∀ x : X, Invertible (l : X.residueField x)]
        [∀ y : Y, Invertible (l : Y.residueField y)] (f : X ⟶ Y)
        (K : sfIntegralConstructibleCategory l E Y)
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : (DerivedCategory.Q (C := scalarReductionSource l E Y)).obj P.obj ≅ K.obj) (n : ℕ),
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map ((β f).hom.app K) ≫
            (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
              (integralSystemTransition l E) f n).hom.app
                ((integralSystemReduction l E Y).obj K) ≫
            (proEtaleConstantRingDerivedPullback
              (Padic.coefficientExtensionRing l E (n + 1)) f).map
                ((integralSystemReductionEvaluation l E Y n).hom.app K) =
          (integralSystemReductionEvaluation l E X n).hom.app
              ((constructibleIntegralPullback l E f).obj K) ≫
            (integralSystemPullbackReductionIso l E f K P e n).hom := by
  sorry

end WeilConjectures
