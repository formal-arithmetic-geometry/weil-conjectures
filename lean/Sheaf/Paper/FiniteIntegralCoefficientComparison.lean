/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.IntegralPullbackCompletedComparisonData

/-! # Finite integral coefficient pullback normalization

Source: Stacks Project, sites-modules.tex, Tags 03EK/03EL; proetale.tex, Tag 099N(5).
(blueprint: lem-a1-finite-integral-coefficient-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
  WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.IntegralOnSlice.hasDerived
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.constantSheaf
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
private instance (priority := 6000) fixedAbSheafify (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private instance (priority := 6000) fixedAbBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W
namespace WeilConjectures.IntegralCompletedComparison
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The two ordinary finite coefficient pullbacks have their normalized comparison.

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL; the finite-generator
part of lem-a1-completed-integral-finite-tower-transport.
(blueprint: lem-a1-finite-integral-coefficient-comparison).

Proof: identify the positive quotient rings by the unique isomorphisms sending
the class of each integral coefficient to its lifted class. The completed ring
isomorphisms intertwine these quotient maps. Inverse image preserves these
coefficient isomorphisms. Associate scalar extension with inverse image and
restrict along the completed projections. Both resulting functors identify with
the sheafification of the balanced inverse-image tensor over the finite quotient.
Send a pure tensor to the same pure tensor under the coefficient isomorphisms;
the inverse uses their inverses. Balancing follows from the projection square.
The maps commute with restrictions and module morphisms, so sheafification gives
a natural isomorphism for every level. The unit coefficient maps to the unit;
hence the pulled quotient-unit generator has exactly the specified completed
finite-generator value. This is FiniteNormalization. The construction works on
the zero module and on the empty site, and uses only positive exponents n+1. -/
theorem finiteIntegral_coefficientComparison
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ e : ∀ n : ℕ, finiteIntegral l E g n ≅ finiteCompleted l E g n,
      ∀ n : ℕ, FiniteNormalization l E g n (e n) := by
  sorry

end WeilConjectures.IntegralCompletedComparison
