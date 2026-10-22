/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.Paper.RingedProjectionRestrictionData

/-! # Signed shifts of a representative-normalized tensor comparison

Source: Stacks Project, Cohomology on Sites, Tag 07A4; More on Algebra, Tag 0FNH.
(blueprint: lem-weil-pbc-ringed-projection-tensor-shifts).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

/-- A tensor comparison already normalized on resolving pairs respects both tensor shifts.
Source: Stacks Project, Tags 07A4 and 0FNH, item-shift-tensor.
(blueprint: lem-weil-pbc-ringed-projection-tensor-shifts).

Proof: write each shift square as equality of natural transformations on the product
of derived categories. Restriction to flat-term K-flat pairs is faithful by tensor
model rigidity, also for the target derived category of the second site. Fix such a
pair P,Q. The normalization fields of sa and sb identify the tensor shifts with the
localized total-complex shift maps. The factors of the exact derived pullback commute
with shifts, as does its termwise cochain functor. Substitute these equations and the
representative equation of t, at P,Q and at the shifted pair. Naturality moves the
localization and exact-functor shift identifications past the comparison. Cancel the
representative isomorphisms and their shifted images. The remaining chain-map square
is checked after every inclusion of a tensor summand. The inverse ordinary comparison
is natural, by transposing under the module adjunction and using its pure-unit equation.
In the first variable both paths send the summand in degrees p,q to degrees p+n,q
without a sign. In the second variable both paths multiply the summand by (-1)^(np).
The pullback is additive, so preserves that sign. Naturality of the ordinary comparison
identifies the remaining factors, and the universal property of the direct sum proves
the chain square. Localizing it proves the restricted square. Faithfulness gives both
squares on arbitrary derived pairs. Shift stability is supplied by the normalization
fields of sa and sb; no bound or nonzero coefficient hypothesis is used. -/
theorem tensorComparison_shifts
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
    {S : Sheaf K CommRingCat.{u + 1}}
    (o : Operation F R S) (a : TensorModel R) (b : TensorModel S)
    (sa : TensorShifts a) (sb : TensorShifts b) (mu : o.OrdinaryTensor)
    (t : TensorComparison o.pullback o.leftModel a b mu.iso) :
    TensorComparisonShifts t (sa := sa) (sb := sb) (sd := inferInstance) := by sorry

end AlgebraicGeometry.Scheme.ProjectionRestriction
