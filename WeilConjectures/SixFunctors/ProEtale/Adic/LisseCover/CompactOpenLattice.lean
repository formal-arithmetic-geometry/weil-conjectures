/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Congruence
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Instances.Matrix

/-!
# Lattices in `Eⁿ` as compact open subgroups

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ`. A *lattice* in `Eⁿ` is a compact open additive
subgroup `L ⊆ Eⁿ` (`PadicAlgCl.CompactOpenLattice E n`); these are the `ℤ_ℓ`-lattices of the
`ℚ_ℓ`-vector space `Eⁿ`. The group `GL_n(E)` acts on them by `g • L = g L`
(`PadicAlgCl.CompactOpenLattice.instMulAction`), and

* the stabilizer of a lattice contains a congruence subgroup
  (`PadicAlgCl.CompactOpenLattice.exists_smul_eq_of_mem_congruenceSubgroup`), so that for
  `γ : Z → GL_n(E)` with continuous entries `z ↦ γ z • L` is locally constant
  (`PadicAlgCl.CompactOpenLattice.isLocallyConstant_smul`);
* the sum of a nonempty finite set of lattices is a lattice
  (`PadicAlgCl.CompactOpenLattice.sum`), compatibly with the action
  (`PadicAlgCl.CompactOpenLattice.smul_sum`).

The sum is what makes a finite orbit of lattices produce a fixed lattice.
-/

@[expose] public section

open Filter Topology Matrix

namespace PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (n : ℕ)

namespace CompactOpenLattice

variable {E n}

section Standard

variable [FiniteDimensional ℚ_[l] E]

end Standard

end CompactOpenLattice

end PadicAlgCl
