/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Paper.IntegralComparisonSystemData
public import Sheaf.Paper.CommonStagePullbackNormalizedDescent

/-! # The coefficient transition equation for normalized automorphism squares

Source: the Weil-structures paragraph of the open-closed localization proof,
steps 7--9 of lem-sf-automorphism-constructible-stage-equivalence.
(blueprint: lem-sf-automorphism-square-stage-compatibility).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- The localized normalized integral square satisfies the scalar transition square.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sf-localization/prop-sf-open-closed-triangle-all-stages.proof.md,
Weil-structures paragraph; steps 7--9 of the automorphism stage-equivalence proof
(blueprint: lem-sf-automorphism-square-stage-compatibility).

Proof: first use the normalized mixed scalar/composition equation for the pairs
(eY,f) and (f,eX). Their composite scheme maps are equal by h. Cancel the two
invertible compositors; the equality gives compatibility of the integral square
with the two composite scalar comparisons. The representative normalization of
IntegralComparisonSystem identifies these scalar comparisons with the prescribed
integralPullbackScalarComparison, independently of the chosen system C.
Apply rational localization to this full morphism equation. The component formula
hb identifies the square components with the localized integral components. The
prescribed object and pure-tensor formulas for rational pullback and coefficient
extension identify the other four arrows with their localized integral maps.
Functoriality of localization then gives the raw rational scalar equation.
Finally substitute commonStagePullbackTransition: each is the raw scalar comparison
conjugated by operationStageTransitionIso. Naturality of these identifications
moves them past the square components. The two intermediate identifications cancel,
leaving exactly the equation below. This includes identity fields, empty schemes,
and semilinear automorphisms, and uses no faithfulness of finite reduction. -/
theorem automorphismSquareStageCompatibility
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (C : IntegralComparisonSystem.{u} l) {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : Y ⟶ X) (eX : Aut X) (eY : Aut Y)
    (h : eY.hom ≫ f = f ≫ eX.hom)
    (a : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      constructibleIntegralPullback l E f ⋙ constructibleIntegralPullback l E eY.hom ≅
        constructibleIntegralPullback l E eX.hom ⋙ constructibleIntegralPullback l E f)
    (ha : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfIntegralConstructibleCategory l E X),
      ((a E).hom.app K).hom =
        (integralComparisonComposition l E C eY.hom f K).inv ≫
          eqToHom (congrArg (fun g ↦ (integralDerivedPullback l E g).obj K.obj) h) ≫
            (integralComparisonComposition l E C f eX.hom K).hom)
    (b : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E eY.hom ≅
        rationalDerivedPullback l E eX.hom ⋙ rationalDerivedPullback l E f)
    (hb : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (K : sfRationalConstructibleCategory l E X),
      HEq ((b E).hom.app K)
        ((sfRationalConstructibleLocalization l E Y).map ((a E).hom.app K.obj)))
    (E L : Index l Ω) (w : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T w).map
        ((b (Coefficient.{u} l Ω E)).hom.app K) ≫
      (commonStagePullbackTransition l Ω f w).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) eX.hom).obj K) ≫
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).map
        ((commonStagePullbackTransition l Ω eX.hom w).hom.app K) =
    ((commonStagePullbackTransition l Ω eY.hom w).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).obj K) ≫
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) eY.hom).map
        ((commonStagePullbackTransition l Ω f w).hom.app K)) ≫
      (b (Coefficient.{u} l Ω L)).hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T w).obj K) := by
  sorry

end WeilConjectures
