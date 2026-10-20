/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit


/-!
# The diagonal unit for the Kummer-normalized projective-line trace

Source: blueprint thm-amb-p1-adjunction and lem-amb-p1-diagonal-integrals.
(blueprint: lem-asd-ordinary-finite-p1-diagonal-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteTensor

/-- The supported diagonal gives a unit for the already specified trace counit.
The decomposition and Chern arrows are inputs; no decomposition is asserted here.
Source: blueprint thm-amb-p1-adjunction.md and its proof;
lem-amb-p1-diagonal-integrals.md and its proof.
(blueprint: lem-asd-ordinary-finite-p1-diagonal-unit).

Proof: On P times_S P, the diagonal is an effective Cartier divisor: on each affine
product chart its equation is u-t, which is monic and is a nonzerodivisor over every
base ring, including after base change. Apply the supported Cartier Kummer map to
this divisor. Its unsupported class is c_1(O(Delta)). On each geometric fibre,
restriction along either projection has degree one, so integration against the
normalized trace is one, by the degree-one Kummer calculation. These are degree-zero
endomorphisms of the constant sheaf; conservative geometric stalks check equality.
For a complex M on P, write M as the direct image from the diagonal of its inverse
image. Invert the diagonal projection map to tensor M with the supported diagonal
class. Apply the projection map for p_2 and inverse proper exchange to reach
q^* Rq_* M tensor A_P(1)[2]. These maps are natural and define eta_M on all complexes.
For the first triangular composite substitute the inverse-projection trace formula:
the projection/exchange mate identities cancel the two diagonal projection maps and
leave integration of the diagonal along p_1, hence the identity on Rq_* M. For the
second triangular composite the same tensor/exchange identities cancel the other
projection maps and leave integration along p_2, hence the identity on q^*K tensor
the shifted line. Finally pull back the diagonal Cartier equation. The supported
Kummer square and the projection/exchange tensor square commute with this pullback.
The decomposition square gives the trace square by inversion and its second
projection. Apply the tensor square to the inverse projection followed by this trace
square and the tensor unitor; this is exactly the counit base-change equation below.
All projections are proper with Noetherian source, so the unbounded proper projection
and exchange results apply, without a boundedness or flatness restriction on M or K. -/
theorem ordinaryFiniteP1_diagonal_unit (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) (c : OrdinaryFiniteP1ChernFamily A N hA)
    (hc : OrdinaryFiniteP1ChernFamilySpec A N hA c)
    (b : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      ((ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S) ≅
        (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧))
    (hb : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      (b S hS).hom = ordinaryFiniteP1KummerMap A N hA t c S hS)
    (hbc : OrdinaryFiniteP1KummerMapBaseChange A N hA t c) :
    (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      ∃ η : 𝟭 (DerivedCategoryModule A (ProjectiveLine S)) ⟶
          ordinaryFinitePushforward A (ProjectiveLine S ↘ S) ⋙
            ordinaryFiniteP1Right A N hA S,
        (∀ M : DerivedCategoryModule A (ProjectiveLine S),
          (ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).map (η.app M) ≫
            (ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app
              ((ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj M) = 𝟙 _) ∧
        (∀ K : DerivedCategoryModule A S,
          η.app ((ordinaryFiniteP1Right A N hA S).obj K) ≫
            (ordinaryFiniteP1Right A N hA S).map
              ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) = 𝟙 _)) ∧
    (∀ {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
      (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤)))
      (K : DerivedCategoryModule A S),
      (ordinaryFinitePullback A f).map
          ((ordinaryFiniteP1TraceCounit A N hA S (b S hS)).app K) =
        ordinaryFiniteP1Exchange A f ((ordinaryFiniteP1Right A N hA S).obj K) ≫
          (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteP1RightBaseChange A N hA t f
              (ordinaryFiniteP1_isUnit N S hS) K).hom ≫
          (ordinaryFiniteP1TraceCounit A N hA S' (b S' hS')).app
            ((ordinaryFinitePullback A f).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
