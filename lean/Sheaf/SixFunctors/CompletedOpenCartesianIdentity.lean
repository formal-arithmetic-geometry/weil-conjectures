/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.OpenBaseChangeSquareData

/-! # Canonical open projection and base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionBaseChange
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
variable (E : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]

/-- The actual completed open maps obey the Cartesian tensor identity on the
bounded constructible domains already supplied. No Tor bound is needed here.

Source: blueprint sec-six-functors/sk-prop-sf-pf-coherence, base-change paragraph,
steps 5--6; Bhatt--Scholze 6.5.5, 6.5.8; Stacks 07A4 and 0GL1.
(blueprint: lem-sf-completed-open-cartesian-identity).

Proof: put V = K tensor JP and W = AK tensor J'HP. Both routes land in j'_!W,
and the first source is isomorphic to j'_!AV by beta_V after H(gamma_j).
The invertible open unit and fully faithful extension imply that restriction
J' detects equality of these arrows. Use the open-factor beta_restriction and
gamma_restriction formulas to compute their restrictions. For the first route,
naturality of the open unit gives mu_A followed by 1 tensor sigma_P. For the
second, tensor monoidality of the canonical pullback-composition square moves
sigma past mu_H. Its first tensor factor cancels the inverse open unit in the
restriction of beta_K; restriction of gamma_j identifies the remaining factor
with mu_A. Thus both restricted maps are the same. The tensor and pullback
comparisons here are the strict quotient normalized comparisons: their
augmentation equations identify the ordinary restriction tensor maps with the
ambient arrows of canonicalIntegralPullbackTensor. This proves equality of
completed morphisms before finite evaluation or rationalization. All stated
domains are supplied explicitly, so each use of the constructible comparison
and each cancellation is defined without imposing finite Tor amplitude on K. -/
theorem completed_open_cartesian_identity
    (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps D c E Q)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left))
    (hK : sfIntegralConstructible c.l E Q.X.obj.left K)
    (dom : IntegralDomains D c E Q K L) :
    IntegralEquation D c E Q d K L hK dom := by sorry

end WeilConjectures.OpenProjectionBaseChange
