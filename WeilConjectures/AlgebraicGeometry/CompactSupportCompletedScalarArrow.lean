/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarComposition

/-! # The completed-linear compact-support scalar arrow

Source: Stacks 0941 and 07A6; the normalized scalar-limit construction in the
auxiliary coefficient-comparison proof, Step 7
(blueprint: def-pur-compact-support-completed-scalar-arrow).

This module re-exports the existing completed arrow and its uniqueness interface.
It introduces no new choice, map, or proof of scalar composition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures.PurScalarArrow

/-- The existing uniqueness theorem for the completed-linear realization of
r_e inverse R(q) tau. Its normalization is an equation after exact restriction to
constant integral coefficients and the canonical total-limit identifications.
Source: Stacks 0941, 07A6; auxiliary normalized scalar-limit construction
(blueprint: def-pur-compact-support-completed-scalar-arrow).
Proof: re-export the existing theorem, with every binder and universe unchanged.
Its proof uses the normalized scalar-limit-reduction comparison for existence
and the derived completion adjunction on complete objects for uniqueness. -/
abbrev completedArrow_existsUnique :=
  @PurStrictScalar.completedArrow_existsUnique.{u}

/-- The existing arrow selected by that unique normalization, with its complete
constructible uniform finite-Tor input and its ramification data retained.
Source: Stacks 0941, 07A6; auxiliary normalized scalar-limit construction
(blueprint: def-pur-compact-support-completed-scalar-arrow). -/
abbrev completedArrow := @PurStrictScalar.completedArrow.{u}

end WeilConjectures.PurScalarArrow
