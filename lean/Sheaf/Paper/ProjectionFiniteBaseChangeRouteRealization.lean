/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteCalculation
import Sheaf.Paper.ProjectionFiniteBaseChangeRightRouteCalculation

/-! # Realization of the two finite base-change routes

Source: prop-sf-pf-coherence, the realization of its displayed base-change square.
(blueprint: lem-sf-finite-base-change-route-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures
variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Each route is carried separately to its fixed-scalar route by the recorded
endpoint comparisons. This asserts compatibility of coordinates, without asserting
that the projection/exchange square commutes in either coordinate system.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, conjugation by the
specified coefficient realization; def-sf-constructible-projection-mates.
(blueprint: lem-sf-finite-base-change-route-realization).

Proof: expand the finite projection component as its source comparison, the realized
fixed component, and its inverse target comparison. The finite exchange is the
realized compactification exchange with its recorded support and pullback comparisons.
For the first route, naturality of pullRealization moves the image of the projection
through the inverse-image comparison. Naturality of supportRealization moves the
last tensor comparison through the support functor. Cancel the intervening coefficient
units and counits using the two equivalence triangle identities. The two restricted
pullback compositors are carried to the fixed derived compositors by
finitePullCompositionNormalization; their composite is the inverse square comparison.
The resulting arrow is precisely diamondLeft. For the second route, expand the
monoidality comparison, use tensor bifunctoriality to move the exchange comparison
through its first variable, and expand the bottom projection. The same unit/counit
cancellations give diamondRight. The surviving endpoint comparisons are the explicit
SquareSource and SquareTarget above in both calculations. This uses only naturality,
functoriality and the prescribed normalization equations, with no invertibility of a
projection or exchange. Zero inputs, empty schemes and identity squares obey the same
calculation; only the second input needs finite Tor amplitude. -/
theorem sixFunctorProjectionFinite_routes_realization
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y
    let R' := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y'
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let source := sixFunctorProjectionFiniteSquareSource S Q K L
    let target := sixFunctorProjectionFiniteSquareTarget S Q K L
    I.map (sixFunctorProjectionFiniteLeftPath S Q K L) ≫ target.hom =
      source.hom ≫ R'.functor.map
        (FiniteProjectionExchange.diamondLeft A Q.square Q.compactification
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) ∧
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫ target.hom =
      source.hom ≫ R'.functor.map
        (FiniteProjectionExchange.diamondRight A Q.square Q.compactification
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) := by
  exact ⟨sixFunctorProjectionFinite_left_route_calculation S Q K L,
    sixFunctorProjectionFinite_right_route_calculation S Q K L⟩

end WeilConjectures
