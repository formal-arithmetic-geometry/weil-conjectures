/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # The finite-rank ell-adic lattice

Source: main-20261015 blueprint, direct-images proof, paragraph (3), the lattice in the
trivial-representation analytic base case (blueprint: def-sfb-ladic-lattice).

This is the finite product of the existing p-adic integers with its product topology.
The universe lift and multiplicative tag only adapt its size and group notation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Profinite.LadicLattice

/-- The rank-r lattice Z_ell^r with its standard product ell-adic topology.
The additive group is written multiplicatively, without changing the topology or law.
Source: direct-images paragraph (3), trivial lattice base case
(blueprint: def-sfb-ladic-lattice). -/
abbrev Lattice (ell r : ℕ) [Fact ell.Prime] :=
  Multiplicative (ULift.{u} (Fin r → ℤ_[ell]))

/-- The existing total disconnectedness of the product, transported along its size lift.
Source: the inverse-limit lattice topology in direct-images paragraph (3)
(blueprint: def-sfb-ladic-lattice). -/
instance latticeTotallyDisconnected (ell r : ℕ) [Fact ell.Prime] :
    TotallyDisconnectedSpace (Lattice.{u} ell r) :=
  Homeomorph.ulift.symm.totallyDisconnectedSpace

end Profinite.LadicLattice
