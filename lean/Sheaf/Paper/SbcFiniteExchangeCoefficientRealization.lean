/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Paper.SbcCompletedOperations
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! # Coefficient realization of the ordinary finite exchange -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Changing from fixed scalars to continuous-function quotient coefficients conjugates
ordinary exchange, before any smoothness, finiteness of morphisms or completion argument.
Source: Stacks, Remark 07A7 and Lemma 0D6D; the coefficient-realization step of blueprint
finite pro-etale smooth base change
(blueprint: lem-sbc-finite-exchange-coefficient-realization).

Proof: let F_W be the exact quotient-coefficient realization at each corner. The
constant-section maps define its inverse equivalence. Underived direct image is
restriction of sections along base change; its comparison with F is identity on those
sections. Its inverse mate identifies inverse images, with the tensor unit sent to
1 tensor m. Derive these comparisons, using exactness of the realizations and their
inverses. The derived direct-image comparison is the unique one compatible with the
localization units; its inverse-image mate preserves the derived unit and counit.
For two composable scheme maps, both direct-image pasting comparisons restrict along
the same canonical isomorphism of iterated fiber products. Their conjugate pullback
comparisons therefore agree. Apply this to the two paths of the square. The finite
coefficient maps used in sbcFiniteTheta are precisely these constant-section maps,
so its square comparison is conjugate to the fixed-scalar square comparison.
Substitute the unit comparison, this square equation, and the counit comparison in
the three-factor definition of sbcFiniteExchangeApp. The resulting commuting square
has invertible source and target comparisons and hence gives the asserted arrow
isomorphism. No exchange map is assumed invertible. The argument also works on empty
schemes and for the zero quotient ring; all units are those of the same equivalences. -/
theorem sbcFiniteExchange_coefficient_realization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g) (n : ℕ)
    (J : DerivedCategory (pbcModules T
      ((pbcAdicRings T (pbcIntegralDatum l E)).obj (Opposite.op n)))) :
    Nonempty (Arrow.mk (sbcFiniteExchangeApp l E sq n J) ≅
      Arrow.mk ((pbcDerivedFunctionRealization X (pbcIntegralDatum l E) n).map
        ((ProEtale.derivedBaseChangeMap
          (ModuleCat.{u + 1} (ProEtale.PbcQuotient (pbcIntegralDatum l E) n))
          sq.toCommSq.flip).app
            ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).asEquivalence.inverse.obj
              J)))) := by
  sorry

end WeilConjectures
