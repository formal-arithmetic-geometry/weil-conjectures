/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.PointSystemPowerRoosData


/-! Specialization of the point-power composition argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PointSystemTransport.PowerRoos
variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The section-normalized compositors and strict insertion identity for recursive powers.
Source: blueprint trace-transport, Step 1, Global powers; Stacks 03CB, 0H7J.
(blueprint: lem-trf-point-power-strict-insertion-specialization).

Proof: identify `pointPower D r` with the rth power of `frobeniusPointIso D` by
induction, using its defining successor equation and the power successor equation.
Apply pointSystemInsertionComposition to this automorphism, with l invertible because
l differs from the characteristic p. For positive r use its index r-1; the zero
power compositors and restriction comparison are the identity-site unit comparisons.
Transport d, t and b along these equalities. Their section equations remain HEq
identities, so coefficient_existsUnique identifies the transported scalar maps with
the maps in PointSystemTransport. The finite tensor compositor is conjugated by the
specified inverseImageFiniteComparisonComplex maps; its tensor-unit equation follows
from TensorLaws, first for the same section and then after transporting the given HEq.
The section equation in StrictInsertionLaws identifies its complexInsertion with u:
compose with the canonical complex composition iso, and use the uniqueness clause of
chainTransport_existsUnique. Its strict chain compositor equation therefore becomes
StrictTransportCoherence, with every original transition and differential retained. -/
theorem point_power_strict_insertion_specialization (hl : l ≠ D.p) :
    ∃ P : Compositors D l E,
      HasSiteSections D l E P ∧ HasSystemSections D l E P ∧
      HasRestrictionSections D l E P ∧ HasTensorUnits D l E P ∧
      ∀ (m : ℕ) (hm : 1 ≤ m), StrictTransportCoherence D l E hl P m hm := by
  sorry

end WeilConjectures.PointSystemTransport.PowerRoos
