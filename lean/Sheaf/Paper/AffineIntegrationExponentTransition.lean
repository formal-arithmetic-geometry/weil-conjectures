/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.VectorIntegrationUnitTranspose

/-! # Root transitions of the ordinary ordered affine transpose

Source: blueprint latest, sec-smooth-purity/sk-prop-an, ordered tower paragraph of
lem-amb-affine-space-top-trace.proof.md; exponent compatibility in
lem-pur-integration-exponent-transpose-transport, Steps 6--9 and 11.
(blueprint: lem-pur-affine-transpose-exponent-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- The compared ordinary affine adjunct is natural in the root-power transition.
There is no vector bundle, frame, or global integration in this statement.
Source: ordered affine trace and exponent transport, Steps 6--9 and 11
(blueprint: lem-pur-affine-transpose-exponent-transition).

Proof: at each exponent use the normalized ordinary projective-line decomposition.
The root-power map sends the unit summand by the shifted root transition and the
Chern summand by identity, since its Kummer boundary is the same coefficient Chern
class. Invert this decomposition to see that the projective trace commutes with
transition. Naturality of the open counit gives the same assertion for the affine
line. Induct on d using the specified composite-adjunction counit to obtain the
ordered affine counit equation, i.e. the ordinary part of IntegrationAffineEquations
in lem-pur-integration-exponent-transpose-transport. The transition on its source
is integrationTowerTransition: conjugation of baseExponentComparison by the two
canonical affineLinearCoefficientDescent maps. Their pullback naturality identifies
it, after base-coefficient pullback, with baseExponentComparison on the tower
itself. The ordinary lower-shriek functor and exceptional adjunction are independent
of the exponent. Source naturality of their Hom bijection therefore carries the
trace equation to the adjunct equation. Apply the exact comparison functor, its
map_comp law, and the HEq endpoint transports defining affineTranspose. At d=0 the
transition is identity and the identity adjunction gives the same equation. All
arguments apply to empty bases and to any finite ramified coefficient level. -/
theorem affineTranspose_exponent_transition (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (d r r' : ℕ) (h : r ≤ r')
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0) :
    (comparison (Ring P) (iteratedAffineLine T d)).map
        (baseExponentComparison P.coefficients.l P.extension (P.level - 1)
          (iteratedAffineLine T d) (primeUnit P _ (towerBase aT d))
          r r' h hA hA' d).hom ≫
      affineTranspose P T aT d r hA = affineTranspose P T aT d r' hA' := by
  sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
