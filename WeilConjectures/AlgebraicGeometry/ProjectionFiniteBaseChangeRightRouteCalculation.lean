/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeCoordinates
import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeLeftRouteCalculation
import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeRightLeftPath
import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeDiamondEquality

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

/-! # Right finite projection/base-change route calculation

Source: prop-sf-pf-coherence, the base-change paragraph.
(blueprint: lem-sf-finite-base-change-right-route-calculation).
-/

/-- The right finite projection route expands to the prescribed fixed-scalar diamond.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, second route.
(blueprint: lem-sf-finite-base-change-right-route-calculation).

Proof: expand `sixFunctorProjectionFiniteRightPath`, `source`, and `target`.
Use bifunctoriality to move the exchange comparison through its first tensor
variable and naturality of the projection component for the bottom map. Cancel
the same coefficient unit and counit as in the left calculation; the pullback
compositors normalize to the fixed derived compositors. The remaining endpoint
comparison is exactly the realization of `diamondRight`. No invertibility of a
projection or exchange is used, and the argument also covers empty objects and
identity squares.
-/
theorem sixFunctorProjectionFinite_right_route_calculation
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
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫ target.hom =
      source.hom ≫ R'.functor.map
        (FiniteProjectionExchange.diamondRight A Q.square Q.compactification
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) := by
  dsimp only
  rw [sixFunctorProjectionFinite_right_left_path S Q K L]
  rw [sixFunctorProjectionFinite_left_route_calculation S Q K L]
  rw [sixFunctorProjectionFinite_diamond_equality S Q K L]
  rfl

end WeilConjectures
