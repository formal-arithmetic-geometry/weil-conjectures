/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
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

/-- The right and left route composites agree before endpoint realization.
Source: prop-sf-pf-coherence.proof.md, base-change paragraph, route normalization.
(blueprint: lem-sf-finite-base-change-right-left-path).

Proof: expand both route composites, use bifunctoriality and the naturality of
the supplied exchange and projection comparisons, and normalize the pullback
compositors. The resulting fixed-coordinate composites are identical. -/
theorem sixFunctorProjectionFinite_right_left_path
    (S : SixFunctorDatum D C E n hn) (Q : SixFunctorCompactifiedSquare D)
    (K : sixFunctorFiniteCategory D C E n hn Q.X)
    (L : finiteTorConstructibleCategory C.l E n hn Q.Y.obj.left) :
    sixFunctorProjectionFiniteRightPath S Q K L =
      sixFunctorProjectionFiniteLeftPath S Q K L := by
  sorry

end WeilConjectures
