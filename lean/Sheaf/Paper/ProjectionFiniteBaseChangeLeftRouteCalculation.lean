/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import Sheaf.Paper.ProjectionFiniteBaseChangeLeftRouteExpansion

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

/-! # Left finite projection/base-change route calculation

Source: prop-sf-pf-coherence, the base-change paragraph.
(blueprint: lem-sf-finite-base-change-left-route-calculation).
-/

/-- The left finite projection route expands to the prescribed fixed-scalar diamond.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, first route.
(blueprint: lem-sf-finite-base-change-left-route-calculation).

Proof: expand `sixFunctorProjectionFiniteLeftPath`, `source`, and `target`. Use
naturality of `pullRealization` to move the realized projection through the
inverse-image comparison, and naturality of `supportRealization` to move the
final tensor comparison through support. Cancel the coefficient unit and
counit by the two equivalence triangle identities. The restricted pullback
compositors rewrite by the finite pull composition normalization, leaving the
source comparison followed by the realization of `diamondLeft`. The calculation
uses only functoriality and the recorded comparison maps and also covers empty
objects and identity squares.
-/
theorem sixFunctorProjectionFinite_left_route_calculation
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
          (RX.inverse.obj K.obj) (RY.inverse.obj L.obj)) := by
  simpa [sixFunctorProjectionFiniteLeftPath] using
    (sixFunctorProjectionFinite_left_route_expansion S Q K L)

end WeilConjectures
