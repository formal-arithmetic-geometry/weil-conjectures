/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates
import all Sheaf.Paper.FiniteProjectionExchangeTransposes

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

/-- The two fixed-scalar projection diamonds agree.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, fixed-coordinate
proper/open mate calculation.
(blueprint: lem-sf-finite-base-change-diamond-equality).

Proof: transpose the proper and exchange composites through the derived
upper-star/lower-star adjunction. Their common transpose is the canonical
open-factor assembly, so injectivity of the adjunction hom equivalence gives
the equality. This is independent of the realization and applies to all
objects, including empty and identity cases. -/
theorem sixFunctorProjectionFinite_diamond_equality
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let RX := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.X
    let RY := CompactSupportFiniteProjection.realization
      (C := C) (E := E) (n := n) (hn := hn) Q.Y
    FiniteProjectionExchange.diamondLeft A Q.square Q.compactification
        (RX.inverse.obj K.obj) (RY.inverse.obj L.obj) =
      FiniteProjectionExchange.diamondRight A Q.square Q.compactification
        (RX.inverse.obj K.obj) (RY.inverse.obj L.obj) := by
  have _datum := S
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  exact FiniteProjectionExchange.diamond_equality _ Q.square Q.compactification _ _

end WeilConjectures
