/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.Paper.ScalarFibreComponentData

/-! # Objectwise scalar fibre maps before naturality and coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- Objectwise scalar maps obtained by finite-free completion and balanced localization.
Source: BS 6.8.4(1),(4),(6), 6.8.14--6.8.15.
(blueprint: lem-per-scalar-fibre-components).

Proof: Use the intrinsic fibre construction and its adapted affine etale lattice charts
from normalized fibre exactness. Use the normalized pullback construction on these same
intrinsic fibres. On a chart reconstruct the scalar lattice by the completed lisse system
comparison: it is the ordinary finite-free tensor over the completed coefficient sheaf.
The realization scalar comparison identifies its rationalization with the actual scalar
heart object and fixes the derived degree-zero presentation map. At target quotient m,
the source uniformizer power ceil(m/e) is zero; the cofinal source exponent m gives the
same tensor and unit. Apply the finite etale stalk scalar theorem to this quotient map,
without assuming it flat. Tower reconstruction identifies its source with the quotient
of the original inverse-limit stalk. Thus the target stalk system is scalarQuotients.
The reduction cone of the scalar tensor is limiting: in a finite basis it is the product
of copies of the complete integer ring. This includes the zero basis. Invert its canonical
map to obtain a, with the stated projection equation. Localize at the target uniformizer;
the source uniformizer is a unit times its ramification power. Balanced associativity
then gives the component iso and its pure-tensor equation. On a common affine refinement,
the same reduction units and realization counits identify the intrinsic computation with
this chart computation. Therefore every specified chart and every degree-zero presentation
has the displayed germ and reduction-cone formulas. No naturality or coherence assertion
about these objectwise scalar components is made in this lemma. -/
theorem scalar_fibre_components :
    ∃ (ω : Fibres (k := k) l R) (α : NormalizedPullback l R ω),
      Nonempty (ScalarFibreComponents l R ω) := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
