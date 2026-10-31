/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeCoordinates
import WeilConjectures.AlgebraicGeometry.ProjectionFiniteBaseChangeRightLeftPathRealized

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

/-- The right and left route composites agree before endpoint realization.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, route normalization.
(blueprint: lem-sf-finite-base-change-right-left-path).

Proof: cancel the target comparison after applying the faithful intrinsic
realization functor. The preceding realized route equality supplies the required
cancellation equation.
-/
theorem sixFunctorProjectionFinite_right_left_path
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    sixFunctorProjectionFiniteRightPath S Q K L =
      sixFunctorProjectionFiniteLeftPath S Q K L := by
  let := Padic.finite_coefficientExtensionRing C.l E n hn
  let I := (intrinsicFiniteTorsionConstructible C.l E n hn Q.Y'.obj.left).ι
  let target := sixFunctorProjectionFiniteSquareTarget S Q K L
  apply I.map_injective
  apply (cancel_mono target.hom).mp
  exact sixFunctorProjectionFinite_right_left_path_realized S Q K L

end WeilConjectures
