/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Semisimple

/-!
# Clifford's theorem

A finite-dimensional semisimple representation restricts semisimply to a normal subgroup.

`Representation.IsSemisimpleRepresentation` is an `abbrev` for the class
`ComplementedLattice (Subrepresentation ρ)`, so the statement is phrased as an instance: the
semisimplicity of the restriction is then available to instance search.

## Main declarations

* `Representation.isSemisimpleRepresentation_comp_subtype`: **Clifford's theorem**.

## Blueprint

`Representation.isSemisimpleRepresentation_comp_subtype` implements part of `sk-i-restriction`.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V) [IsSemisimpleRepresentation ρ]
  (N : Subgroup G) [N.Normal]

/-- **Clifford's theorem**: a finite-dimensional semisimple representation restricts semisimply
to a normal subgroup.
(blueprint: `sk-i-restriction`) -/
instance isSemisimpleRepresentation_comp_subtype :
    IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  sorry

end Representation
