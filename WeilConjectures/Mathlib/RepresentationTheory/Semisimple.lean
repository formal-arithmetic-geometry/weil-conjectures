/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# Clifford's theorem

A finite-dimensional semisimple representation restricts semisimply to a normal subgroup.

`Representation.IsSemisimpleRepresentation` is an `abbrev` for the class
`ComplementedLattice (Subrepresentation ρ)`, so the statement is phrased as an instance: the
semisimplicity of the restriction is then available to instance search.

## Main declarations

* `Representation.isSemisimpleRepresentation_comp_subtype`: **Clifford's theorem**.
* `Representation.isSemisimpleRepresentation_of_isInternal`: an internal direct sum of irreducible
  subrepresentations is semisimple.

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

namespace Representation

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A representation that is the internal direct sum of irreducible subrepresentations is
semisimple. -/
theorem isSemisimpleRepresentation_of_isInternal {G : Type*} [Monoid G]
    {ρ : Representation k G V} {ι : Type*} [DecidableEq ι] (Vs : ι → Subrepresentation ρ)
    (hirr : ∀ j, IsIrreducible (Vs j).toRepresentation)
    (hdirect : DirectSum.IsInternal fun j ↦ (Vs j).toSubmodule) :
    IsSemisimpleRepresentation ρ := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule'
    (p := fun j ↦ (Vs j).asSubmodule) (fun j ↦ ?_) ?_
  · have : IsSimpleModule (MonoidAlgebra k G) (Vs j).asSubmodule := by
      rw [isSimpleModule_iff_isAtom]
      exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff _).2
        (Subrepresentation.isAtom_of_isIrreducible (hirr j))
    infer_instance
  · refine eq_top_iff.2 ?_
    rintro x -
    have hx : (x : V) ∈ ⨆ j, (Vs j).toSubmodule :=
      hdirect.submodule_iSup_eq_top ▸ Submodule.mem_top
    induction hx using Submodule.iSup_induction' with
    | mem j y hy => exact Submodule.mem_iSup_of_mem (p := fun j ↦ (Vs j).asSubmodule) j hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz

end Representation
