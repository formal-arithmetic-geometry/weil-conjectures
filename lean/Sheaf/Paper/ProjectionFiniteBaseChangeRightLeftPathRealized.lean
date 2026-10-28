/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates

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

/-- Realized equality of the right and left finite projection routes.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, route normalization.
(blueprint: lem-sf-finite-base-change-right-left-path-realized).

Proof (postponed): expand both route composites through the source and target
comparisons, apply bifunctoriality and naturality of the exchange and projection
maps, and normalize the pullback compositors. The resulting fixed-coordinate
composites are the two fixed projection diamonds; the canonical proper/open mate
calculation identifies them. Applying the intrinsic realization and composing with
the target comparison gives the displayed equality.
-/
theorem sixFunctorProjectionFinite_right_left_path_realized
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
    let target := sixFunctorProjectionFiniteSquareTarget S Q K L
    I.map (sixFunctorProjectionFiniteRightPath S Q K L) ≫ target.hom =
      I.map (sixFunctorProjectionFiniteLeftPath S Q K L) ≫ target.hom := by
  sorry

end WeilConjectures
