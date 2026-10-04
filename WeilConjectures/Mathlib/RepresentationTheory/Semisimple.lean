/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple

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

/-- A subrepresentation `S` that is irreducible as a representation is an atom of the lattice of
subrepresentations. -/
theorem _root_.Subrepresentation.isAtom_of_isIrreducible {G : Type*} [Monoid G]
    {ρ : Representation k G V} {S : Subrepresentation ρ} (hS : IsIrreducible S.toRepresentation) :
    IsAtom S := by
  let restrict (T : Subrepresentation ρ) : Subrepresentation S.toRepresentation :=
    ⟨T.toSubmodule.comap S.toSubmodule.subtype, fun g x hx ↦ T.apply_mem_toSubmodule g hx⟩
  have := hS
  refine ⟨fun h ↦ ?_, fun T hT ↦ ?_⟩
  · refine (bot_ne_top : (⊥ : Subrepresentation S.toRepresentation) ≠ ⊤) ?_
    ext x
    have : (x : V) = 0 := by
      have hx : (x : V) ∈ (⊥ : Subrepresentation ρ) := h ▸ x.2
      exact (Submodule.mem_bot k).1 hx
    exact ⟨fun _ ↦ Submodule.mem_top, fun _ ↦ (Submodule.mem_bot k).2 (Subtype.ext this)⟩
  · rcases IsSimpleOrder.eq_bot_or_eq_top (restrict T) with h | h
    · refine le_antisymm (fun x hx ↦ ?_) bot_le
      have : (⟨x, hT.le hx⟩ : S.toSubmodule) ∈ restrict T := hx
      rw [h] at this
      exact (Submodule.mem_bot k).2 (congrArg Subtype.val ((Submodule.mem_bot k).1 this))
    · refine absurd (fun x hx ↦ ?_) hT.not_ge
      have : (⟨x, hx⟩ : S.toSubmodule) ∈ restrict T := h ▸ Submodule.mem_top
      exact this

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
