/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RingTheory.Artinian.Module
public import Submission.WeilConjectures.Mathlib.RepresentationTheory.Invariants
public import Submission.WeilConjectures.Mathlib.RepresentationTheory.Irreducible
public import Submission.WeilConjectures.Mathlib.RepresentationTheory.Subrepresentation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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
* `Representation.IsIrreducible.eq_one_of_isConstituent_trivial`: a normal subgroup with a
  trivial constituent in an irreducible representation acts trivially.
* `Representation.isSemisimpleRepresentation_of_isInternal`: an internal direct sum of irreducible
  subrepresentations is semisimple.
* `Representation.isSemisimpleRepresentation_iff_exists_iSupIndep`: a finite-dimensional
  representation is semisimple if and only if it is a direct sum of irreducible
  subrepresentations.

## Blueprint

`Representation.isSemisimpleRepresentation_comp_subtype` implements part of `sk-i-restriction`,
`lem-mg-normal-restriction-semisimple` and `lem-wf-finite-index-restriction-semisimple` (whose
finite-index hypothesis is not needed).
`Representation.IsIrreducible.eq_one_of_isConstituent_trivial` is the case `a = 0` of
`lem-a1-unramified-nonexceptional`.
`Representation.isSemisimpleRepresentation_iff_exists_iSupIndep` is `def-wf-semisimple-module`.
-/

@[expose] public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (ρ : Representation k G V) [IsSemisimpleRepresentation ρ]
  (N : Subgroup G) [N.Normal]

/-- **Clifford's theorem**: a finite-dimensional semisimple representation restricts semisimply
to a normal subgroup, with no finiteness assumption on the quotient.
(blueprint: `sk-i-restriction`, `lem-mg-normal-restriction-semisimple`,
`lem-wf-finite-index-restriction-semisimple`) -/
instance isSemisimpleRepresentation_comp_subtype :
    IsSemisimpleRepresentation (ρ.comp N.subtype) := by
  set σ : Representation k N V := ρ.comp N.subtype
  let e : Subrepresentation σ ≃o Submodule (MonoidAlgebra k N) (Representation.asModule σ) :=
    Subrepresentation.subrepresentationSubmoduleOrderIso
  have : WellFoundedLT (Subrepresentation σ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule)
      fun _ _ h ↦ lt_of_le_of_ne h.le fun h' ↦ h.ne (Subrepresentation.toSubmodule_injective h')
  have : IsAtomic (Subrepresentation σ) := inferInstance
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

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A finite-dimensional representation is semisimple if and only if it is a direct sum of
irreducible subrepresentations: there is a set of irreducible subrepresentations whose underlying
subspaces are independent and span `V`. (blueprint: `def-wf-semisimple-module`) -/
theorem isSemisimpleRepresentation_iff_exists_iSupIndep [FiniteDimensional k V]
    {ρ : Representation k G V} :
    IsSemisimpleRepresentation ρ ↔ ∃ s : Set (Subrepresentation ρ),
      (∀ U ∈ s, U.toRepresentation.IsIrreducible) ∧
        iSupIndep (fun U : s ↦ U.1.toSubmodule) ∧ ⨆ U : s, U.1.toSubmodule = ⊤ := by
  constructor
  · intro
    obtain ⟨s, hind, htop, hat⟩ := exists_sSupIndep_of_sSup_atoms_eq_top
      (sSup_atoms_eq_top (α := Subrepresentation ρ))
    refine ⟨s, fun U hU ↦ Subrepresentation.isIrreducible_toRepresentation_iff_isAtom.2 (hat hU),
      Subrepresentation.iSupIndep_toSubmodule_iff.2 ((sSupIndep_iff s).1 hind), ?_⟩
    rw [← Subrepresentation.toSubmodule_iSup, ← sSup_eq_iSup', htop]
    rfl
  · rintro ⟨s, hirr, hind, htop⟩
    classical
    exact isSemisimpleRepresentation_of_isInternal (fun U : s ↦ U.1) (fun U ↦ hirr U.1 U.2)
      (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop)

end Representation
