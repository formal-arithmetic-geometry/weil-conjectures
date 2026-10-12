/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
import Sheaf.AlgebraicGeometry.DivisorModule
import Sheaf.AlgebraicGeometry.FunctionField

/-! # Divisor restriction across a smooth curve compactification -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A principal divisor on the open curve has a principal extension with identical orders.
Source: blueprint, sec-curve-estimates/sk-prop-cd-affine/lem-sc-pic-affine, first paragraph,
restriction and boundary divisors
(blueprint: lem-sc-principal-divisor-open-extension).

Proof: a nonempty open subset of an integral scheme contains its generic point. Hence the
open immersion of the connected smooth curve into its integral compactification identifies
both generic stalks, and thus both function fields. Transport the given unit through the
inverse of this field isomorphism to a unit b on Z. At Q and its image P the open immersion
identifies local rings and the maps into the common function field. The discrete valuation
rings therefore have identical normalized valuations: a uniformizer maps to a uniformizer,
and units map to units. Applying this to the given rational function yields the displayed
coefficient equality. No choice of a divisor or trivial Picard class is used, and no boundary
order is prescribed. For a constant unit all retained orders vanish; an empty boundary
simply makes the equality hold at every ambient closed point. -/
theorem Scheme.Hom.exists_principal_divisor_open_extension
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [IsIntegral C] [IsNoetherian C] [IsIntegral c.Z] [IsNoetherian c.Z]
    (a : Additive C.functionFieldˣ) :
    ∃ b : Additive c.Z.functionFieldˣ,
      ∀ (P : closedPoints c.Z) (Q : closedPoints C), c.i.base Q.val = P.val →
        c.Z.div b P = C.div a Q := by sorry

end AlgebraicGeometry
