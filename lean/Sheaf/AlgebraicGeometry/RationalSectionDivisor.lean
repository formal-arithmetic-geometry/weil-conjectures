/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.AlgebraicGeometry.RationalSectionOrder
import WeilConjectures.AlgebraicGeometry.Curve.Divisor

/-!
# Rational sections and their divisors on smooth connected curves

Source: Stacks Project, Divisors, Tags 01X5 (2), 02SF and 0BE6 (1)
(blueprint: def-sc-rational-section-divisor).

## Main definitions

- `rationalSection`: the generic stalk of the invertible module.
- `rationalSectionOrder`: the normalized valuation of its coefficient in a local generator.
- `rationalSectionDivisor`: the finite sum of these orders at closed points.

Integrality is obtained from `smooth_connected_curve_local_rings`, not assumed separately.
The coefficient exists because `invertible_module_generic_stalk` identifies the image of
any local generator with a basis of the generic stalk. `rational_section_order` makes its
valuation independent of the generator and supplies the finite set used in the sum.
-/

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A rational section is an element of the generic stalk; nonzero means unequal to zero
in this additive group. The generic stalk is a one-dimensional vector space over the
function field by `invertible_module_generic_stalk`.
Source: Stacks Project, Tag 01X5 (2) (blueprint: def-sc-rational-section-divisor). -/
noncomputable abbrev rationalSection
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) : Type u :=
  letI := Classical.choose (C.smooth_connected_curve_local_rings k f)
  ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint C))

/-- The order of a nonzero rational section at a closed point. Choose the integer obtained
from some local generator and its nonzero coefficient. Such a coefficient exists by
`invertible_module_generic_stalk`; all choices give the same integer by
`rational_section_order`. The valuation is the normalized DVR valuation from
`smooth_connected_curve_local_rings`.
Source: Stacks Project, Tag 02SF (blueprint: def-sc-rational-section-divisor). -/
noncomputable def rationalSectionOrder
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) [L.IsInvertible]
    (s : {s : rationalSection k C f L // s ≠ 0}) (P : closedPoints C) : ℤ :=
  letI := Classical.choose (C.smooth_connected_curve_local_rings k f)
  let h := Classical.choose_spec (C.smooth_connected_curve_local_rings k f)
  let lam := TopCat.Presheaf.stalkSpecializes L.val.presheaf
    ((genericPoint_spec C).specializes (Set.mem_univ P.val))
  let v := Classical.choose ((h.2.2.2.2.2.2.2.2 P.val P.property).2.2)
  Classical.epsilon fun n : ℤ ↦
    ∃ e : ↑(TopCat.Presheaf.stalk L.val.presheaf P.val),
      Submodule.span (C.presheaf.stalk P.val) {e} = ⊤ ∧
      ∃ g : C.functionFieldˣ,
        s.val = (g : C.functionField) • lam e ∧ Multiplicative.toAdd (v g) = n

open Classical in
/-- The divisor of a nonzero rational section, the sum of its orders times the closed
points. The finite set is exactly the set of points admitting a coefficient of nonzero
valuation, from `rational_section_order`; all omitted coefficients are zero.
For the structure sheaf, taking the local generator 1 gives the normalized valuation of
the rational function itself, hence the principal divisor `Scheme.div`.
Source: Stacks Project, Tag 0BE6 (1) (blueprint: def-sc-rational-section-divisor). -/
noncomputable def rationalSectionDivisor
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (L : C.Modules) [L.IsInvertible]
    (s : {s : rationalSection k C f L // s ≠ 0}) : C.Divisor :=
  letI := Classical.choose (C.smooth_connected_curve_local_rings k f)
  let hfin := (rational_section_order k C f L s.val s.property).2
  hfin.toFinset.sum fun P ↦
    if hP : P ∈ closedPoints C then
      Finsupp.single ⟨P, hP⟩ (rationalSectionOrder k C f L s ⟨P, hP⟩)
    else 0

end AlgebraicGeometry.Scheme.Modules
