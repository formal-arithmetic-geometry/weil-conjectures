/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.PointFrobeniusNormalizationDefinitions

/-! Canonical point-comparison component of Frobenius normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointFrobeniusNormalization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identity structural exchange and its point-transport recipe, before multiplication.
Source: point normalization steps 3--4; blueprint def-weil-frobenius-coefficient-twists,
Natural Weil isomorphism; Deligne, Weil II (1.1.7), pp. 150--151
(blueprint: lem-pur-point-identity-exchange-recipe).

Proof: express the finite exchange as the mate of the canonical pullback square.
The two compositors with the identity have the same tensor-unit normalization.
Under the identity pullback comparison their values on x tensor one are identities;
tensor generation and sheafification therefore identify the entire square map.
Expand the mate into unit, square map and counit. The adjunction triangles and the
right-adjoint uniqueness comparison give the first exchange equation. For integral
coefficients perform this calculation on the entire strict system category, using
integralComparisonSystemUnit and its unit-normalized compositors, then derive it.
Apply the actual total-limit functor and use naturality and the triangles of the
reduction/limit adjunction. The completion-unit inverse in integralDirectId is valid
on constructible inputs, as is its pullback, by the complete/effective fields of the
specified models. This gives the integral exchange equation as an equality of whole
maps, without detecting derived maps by finite evaluations. Finally expand finiteOrdinary
and integralOrdinary. Naturality of point transport along the identity-direct-image
isomorphism cancels its two identity identifications. The point transport definition
is sigma followed by sections of the specified kappa; exact-functor localization
comparisons cancel, independently of the chosen representative or resolution.
This proves the two recipe equations. Zero objects satisfy the same triangle identities. -/
theorem pointIdentityExchangeRecipe :
    (∀ (n : ℕ)
      (N : proEtaleDerivedCategory (Spec (.of D.k))
        (Padic.coefficientExtensionRing l E (n + 1))),
    (finiteDerivedPullback l E n (frobeniusPointIso D).hom).map
        ((finiteDirectId D l E n).hom.app N) =
      (FrobeniusExchange.finiteExchange (Padic.coefficientExtensionRing l E (n + 1))
        (𝟙 (Spec (.of D.k))) (𝟙 (Spec (.of D.k)))
        (frobeniusPointIso D).hom (frobeniusPointIso D).hom
        ((Category.comp_id _).trans (Category.id_comp _).symm)).app
          N ≫
      (finiteDirectId D l E n).hom.app
        ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
          N) ) ∧
    (∀ (n : ℕ)
      (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ),
      finiteOrdinary D l hl E n (DerivedCategory.Q.obj K) =
        frobeniusPointFiniteSigmaDerived D l E n (DerivedCategory.Q.obj K) ≫
          ((pointFiniteSections D.k
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u + 2, u + 1}).map
              (finiteKappa D l hl E n K)) ∧
    (∀ N : sfIntegralConstructibleCategory l E (Spec (.of D.k)),
    (integralDerivedPullback l E (frobeniusPointIso D).hom).map
      (integralDirectId D l E N.obj) =
      integralExchange D l hl E N ≫ integralDirectId D l E
        ((integralDerivedPullback l E (frobeniusPointIso D).hom).obj
          N.obj) ∧
      integralOrdinary D l hl E N = frobeniusPointIntegralSigmaDerived D l E N.obj ≫
        (pointFibreIntegralAmbient D l E).map
          (inverseImagePullbackComparisonDerived l E (frobeniusPointIso D).hom
            (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) N.obj)) := by
  sorry

end WeilConjectures.PointFrobeniusNormalization
