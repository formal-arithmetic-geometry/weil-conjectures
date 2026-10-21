/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DecompositionMaps

/-! # The two ordinary projective-line components commute with arbitrary base change

Source: main-20261015, thm-amb-p1-decomposition.proof.md, Cartier class and base change
(blueprint: lem-asd-ordinary-finite-p1-kummer-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The actual scalar Kummer class pulls back to the actual scalar Kummer class,
and its evaluation adjunct, as well as the constant unit, commutes with exchange.
This is a statement about the two components, with no splitting or invertibility
assertion and no Noetherian assumption.
Source: main-20261015, thm-amb-p1-decomposition.proof.md, arbitrary-base paragraph
(blueprint: lem-asd-ordinary-finite-p1-kummer-base-change).

Proof: let D be the hyperplane x_0=0. On x_1 nonzero its ideal is (s), where
s=x_0/x_1, and on x_0 nonzero its ideal is the unit ideal. Multiplication by s in
B[s] is injective for every ring B by comparison of coefficients, including after
arbitrary base change. Thus D and its pullback D' are effective Cartier divisors.
The dual ideal frames e_0=1 and e_1=s^{-1} satisfy e_0=t^{-1}e_1, so their line
bundles are exactly the specified O(1). Apply ordinary_supported_kummer to D and
the Cartier pullback D'. Its boundary determines the classes uniquely. Its unit
and Chern equation identifies the first class with c by the assumed specification;
the pulled-back boundary supplies c' with the displayed specification. The supported
pullback square, followed by the mate unit identity for the divisor square, gives
the Chern-class pullback equation, with the canonical normalized twist comparison.
For the projective-line square the mate unit identity gives the constant component
equation. For the second component the mate counit identity identifies its adjunct
with pullback of the adjunct defining h. Inverse image preserves tensor and the
unit, signed shifts and evaluation; the evaluation equation is the normalized
negative-twist equation in etaleFiniteTwistPullback, transported through the canonical
degree-zero and shift comparisons. Substitute the Chern-class pullback equation.
The result is the adjunct defining h' after the negative-twist pullback comparison.
Injectivity of the adjunction correspondence proves the second component equation.
No proper-exchange invertibility is used, and no flatness of A over Z/N is required.
This proof also applies to zero coefficients, N=1, empty bases and nonreduced bases. -/
theorem ordinaryFiniteP1_components_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) c) :
    ∃ c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S'
        ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
          hS'.map (ProjectiveLine S' ↘ S').appTop.hom) c' ∧
      ((ordinaryFinitePullback A g).map (p1DecompositionUnit A S) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
        (ordinaryFiniteUnitPullback A g).hom ≫ p1DecompositionUnit A S') ∧
      ((ordinaryFinitePullback A g).map (p1DecompositionChernAdjoint A N hN hA S hS c) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
        (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom ≫
          p1DecompositionChernAdjoint A N hN hA S' hS' c') := by sorry

end AlgebraicGeometry.Etale
