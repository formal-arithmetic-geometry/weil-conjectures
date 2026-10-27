/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompleteCompactificationLimitSupport

/-! # Direct image and fixed-coefficient strict limits
Source: blueprint direct-image proof, paragraph (2); Stacks 0A07, 0D6E.
(blueprint: lem-sp-compactification-push-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Fixed-tower direct-image evaluation and the projections of its specified limit mate.

Proof. Apply ringedTowerPushforwardLimitComparison to the actual completed-coefficient
ringed geometric morphism of p. Transport its right derived functors and exact
evaluations by their unique localization comparisons to the already specified functors.
The K-injective evaluation equation in that theorem becomes the first displayed
identity after composing the exact evaluation factors and canceling the invertible
derived units. The two ways of composing the pullback/constant-tower adjunction have
the same left adjoint comparison, the identity constant-diagram square. Uniqueness of
right adjoints identifies the theorem's limit comparison with pushLimit, which was
defined by conjugating that same square. Its final projection equation, followed by
the inverse evaluation comparison, gives the second displayed identity. Thus this is
an equality for the specified mate and actual derived projections. No test for equality
of arbitrary derived morphisms by finite evaluation is used. No properness is needed:
the argument uses the ringed direct-image adjunction for an arbitrary p, including the
identity and maps of empty schemes.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2);
parent node step 3; Stacks 0A07, lemma-Rf-commutes-with-Rlim, and 0D6E,
lemma-derived-pushforward-composition.
(blueprint: lem-sp-compactification-push-limit). -/
theorem compactificationPushLimit {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    ∃ w : ∀ n : ℕ, (fixedPushOrd l E p).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E Z n ⋙ (pushOrd l E p).rightDerivedFunctor,
    (∀ n : ℕ,
      ∀ (I : CochainComplex (Fixed l E Z) ℤ) [I.IsKInjective],
    (fixedEvaluation l E Y n).mapDerivedCategory.map
        ((fixedPushOrd l E p).rightDerivedFunctorObjQIso I).hom ≫
      (fixedEvaluation l E Y n).mapDerivedCategoryFactors.hom.app
        (((fixedPushOrd l E p).mapHomologicalComplex (.up ℤ)).obj I) =
    (w n).hom.app (DerivedCategory.Q.obj I) ≫
      (pushOrd l E p).rightDerivedFunctor.map
        ((fixedEvaluation l E Z n).mapDerivedCategoryFactors.hom.app I) ≫
      ((pushOrd l E p).rightDerivedFunctorObjQIso
        (((fixedEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj I)).hom) ∧
    ∀ (K : DerivedCategory (Fixed l E Z)) (n : ℕ),
      (pushLimit l E p).hom.app K ≫
          (coefficientConstantTowerProjection l E Y n).app
            (((fixedPushOrd l E p).rightDerivedFunctor).obj K) =
        (pushOrd l E p).rightDerivedFunctor.map
          ((coefficientConstantTowerProjection l E Z n).app K) ≫ (w n).inv.app K := by sorry

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
