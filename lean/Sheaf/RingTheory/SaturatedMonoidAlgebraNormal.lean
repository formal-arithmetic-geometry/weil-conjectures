/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.AlgebraicGeometry.FineFanBlowup
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integral closedness of saturated monoid algebras

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, Lemma 3.2.9, printed p. 104
(blueprint: lem-trf-saturated-monoid-algebra-normal).

We use multiplicative notation, as in `AlgebraicGeometry.FineFan.saturation`.
Applying the statement to `Multiplicative G` gives its additive formulation.
-/

set_option autoImplicit false

universe u v

namespace MonoidAlgebra

/-- A saturated finitely generated submonoid of a torsion-free abelian group, whose
canonical group completion is that ambient group, has monoid algebra integrally closed
in the ambient group algebra. Integrality and membership use the canonical monomial map.

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, Lemma 3.2.9, printed p. 104
(blueprint: lem-trf-saturated-monoid-algebra-normal).

Proof (the agent deduction recorded in the DAG):
1. Write `x` as its finite sum of nonzero monomials. Apply
   `lem-trf-integral-support-saturation` with `P = Q`: finite generation, torsion-freeness
   and integrality imply that every exponent in its support belongs to the saturation of `Q`.
2. The canonical completion hypothesis identifies the ambient group with the completion
   of `Q`. Saturation, in the conventions of `def-trf-fine-fan-blowup`, therefore puts
   every such exponent in `Q` itself.
3. Restrict the finite coefficient function of `x` to `Q`. This gives `y` in `k[Q]`
   whose image under the canonical monomial inclusion is `x`. The map is injective
   because the exponent inclusion is injective. For empty support take `y = 0`.
   Thus every integral element lies in the image of `k[Q]`, as asserted. -/
theorem saturated_monoid_algebra_normal
    (k : Type u) [Field k] (G : Type v) [CommGroup G] [IsMulTorsionFree G]
    (Q : Submonoid G) (hfg : Q.FG)
    (hsat : AlgebraicGeometry.FineFan.saturation Q = Q)
    (hcompletion : Function.Bijective (Algebra.GrothendieckGroup.lift Q.subtype))
    (x : MonoidAlgebra k G)
    (hx : (MonoidAlgebra.mapDomainRingHom k Q.subtype).IsIntegralElem x) :
    ∃ y : MonoidAlgebra k Q, MonoidAlgebra.mapDomainRingHom k Q.subtype y = x := by
  sorry

end MonoidAlgebra
