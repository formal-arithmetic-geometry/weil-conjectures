/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.Artinian.Module
public import WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

/-!
# Clifford's theorem

A finite-dimensional semisimple representation restricts semisimply to a normal subgroup.

`Representation.IsSemisimpleRepresentation` is an `abbrev` for the class
`ComplementedLattice (Subrepresentation ρ)`, so the statement is phrased as an instance: the
semisimplicity of the restriction is then available to instance search.

The proof follows Clifford: inside the lattice of `N`-subrepresentations, the join `T` of all
simple `N`-subrepresentations is stable under the translations by `G`, which permute the simple
`N`-subrepresentations. Hence `T` is a `G`-subrepresentation; a `G`-complement of `T` would contain
a simple `N`-subrepresentation if it were nonzero, so `T` is everything, and a module that is a sum
of simple submodules is semisimple. No finiteness of `G ⧸ N` is used.

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
  set σ : Representation k N V := ρ.comp N.subtype
  let e : Subrepresentation σ ≃o Submodule (MonoidAlgebra k N) (Representation.asModule σ) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have : WellFoundedLT (Subrepresentation σ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule)
      fun _ _ h ↦ lt_of_le_of_ne h.le fun h' ↦ h.ne (Subrepresentation.toSubmodule_injective h')
  have : IsAtomic (Subrepresentation σ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have : IsAtomic (Submodule (MonoidAlgebra k N) (Representation.asModule σ)) :=
    e.isAtomic_iff.1 this
  rw [IsSemisimpleRepresentation, e.complementedLattice_iff]
  apply complementedLattice_of_sSup_atoms_eq_top
  -- `T` is the join of the simple `N`-subrepresentations; translations by `G` permute them.
  set T := sSup {a : Submodule (MonoidAlgebra k N) (Representation.asModule σ) | IsAtom a}
  have hT (g : G) : e (Subrepresentation.translate ρ N g (e.symm T)) ≤ T := by
    let τ := e.symm.trans ((Subrepresentation.translate ρ N g).trans e)
    change τ T ≤ T
    rw [OrderIso.map_sSup]
    exact iSup₂_le fun a ha ↦ le_sSup ((τ.isAtom_iff a).2 ha)
  let T' : Subrepresentation ρ :=
    ⟨(e.symm T).toSubmodule, fun g v hv ↦ by
      refine e.le_symm_apply.2 (hT g) (Subrepresentation.mem_translate.2 ?_)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      exact hv⟩
  obtain ⟨C, hC⟩ := exists_isCompl T'
  let C' : Subrepresentation σ := ⟨C.toSubmodule, fun n _ hv ↦ C.apply_mem_toSubmodule n hv⟩
  -- A nonzero complement would contain a simple `N`-subrepresentation, which lies in `T`.
  have hC' : C' = ⊥ := by
    rcases eq_bot_or_exists_atom_le C' with h | ⟨a, ha, haC⟩
    · exact h
    have haT : e a ≤ T := le_sSup ((e.isAtom_iff a).2 ha)
    refine (ha.1 (SetLike.ext fun v ↦ ⟨fun hv ↦ ?_, fun hv ↦ ?_⟩)).elim
    · have h : v ∈ T' ⊓ C := ⟨(e.le_symm_apply.2 haT) hv, haC hv⟩
      rw [hC.inf_eq_bot] at h
      exact h
    · change v = 0 at hv
      rw [hv]
      exact a.toSubmodule.zero_mem
  have hCbot : C = ⊥ := Subrepresentation.toSubmodule_injective congr(($hC').toSubmodule)
  have hT'top : T' = ⊤ := by simpa [hCbot] using hC.sup_eq_top
  rw [← e.apply_symm_apply T, eq_top_iff]
  intro v _
  have hv : v ∈ T' := by rw [hT'top]; trivial
  exact (Subrepresentation.mem_asSubmodule_iff (σ := e.symm T) (v := v)).2 hv

end Representation
