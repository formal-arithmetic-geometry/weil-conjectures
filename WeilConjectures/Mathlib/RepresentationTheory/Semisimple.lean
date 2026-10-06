/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import WeilConjectures.Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Clifford's theorem

A finite-dimensional semisimple representation restricts semisimply to a normal subgroup.

`Representation.IsSemisimpleRepresentation` is an `abbrev` for the class
`ComplementedLattice (Subrepresentation ρ)`, so the statement is phrased as an instance: the
semisimplicity of the restriction is then available to instance search.

## Main declarations

* `Representation.isSemisimpleRepresentation_comp_subtype`: **Clifford's theorem**.
* `Representation.IsIrreducible.eq_one_of_isConstituent_trivial`: a normal subgroup with a
  trivial constituent in an irreducible representation acts trivially.

## Blueprint

`Representation.isSemisimpleRepresentation_comp_subtype` implements part of `sk-i-restriction`.
`Representation.IsIrreducible.eq_one_of_isConstituent_trivial` is the case `a = 0` of
`lem-a1-unramified-nonexceptional`.
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

omit [FiniteDimensional k V] [IsSemisimpleRepresentation ρ] in
/-- A normal subgroup `N` such that the trivial one-dimensional representation is a constituent
of an irreducible finite-dimensional representation `V` acts trivially on `V`. The restriction
`V|_N` is semisimple (`Representation.isSemisimpleRepresentation_comp_subtype`), so the
trivial subquotient `B / A` splits off: a complement `C` of `A` meets the class of `B / A` in a
nonzero `N`-invariant vector. The `N`-invariants are then nonzero, and they are all of `V`
(`Representation.IsIrreducible.eq_one_of_invariants_ne_bot`).
(blueprint: `lem-a1-unramified-nonexceptional`, the case `a = 0`) -/
theorem IsIrreducible.eq_one_of_isConstituent_trivial [FiniteDimensional k V] [IsIrreducible ρ]
    (h : (trivial k N k).IsConstituent (ρ.comp N.subtype)) {g : G} (hg : g ∈ N) : ρ g = 1 := by
  refine IsIrreducible.eq_one_of_invariants_ne_bot ρ N ?_ hg
  obtain ⟨-, A, B, -, ⟨e⟩⟩ := h
  -- the class of `B / A` corresponding to `1 ∈ k`
  set one : (trivial k N k).asModule := (trivial k N k).asModuleEquiv.symm 1
  obtain ⟨⟨m, hmB⟩, hm⟩ := Submodule.Quotient.mk_surjective _ (e one)
  have hmA : Representation.asModuleEquiv (ρ.comp N.subtype) m ∉ A := fun hmA ↦ by
    have h0 : e one = e 0 := by
      rw [← hm, map_zero, Submodule.Quotient.mk_eq_zero]
      exact hmA
    exact one_ne_zero ((trivial k N k).asModuleEquiv.symm.injective
      ((e.injective h0).trans (map_zero _).symm))
  have hfix (n : N) : ρ n (Representation.asModuleEquiv (ρ.comp N.subtype) m) -
      Representation.asModuleEquiv (ρ.comp N.subtype) m ∈ A := by
    have h1 : MonoidAlgebra.single n (1 : k) • e one = e one := by
      rw [← map_smul, single_smul, one_smul]
      rfl
    rw [← hm, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h1
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
      Submodule.coe_smul, single_smul, one_smul] at h1
    exact h1
  set m' := Representation.asModuleEquiv (ρ.comp N.subtype) m
  clear_value m'
  have : IsSemisimpleRepresentation ρ := inferInstance
  obtain ⟨C, hC⟩ := exists_isCompl A
  have hmem : m' ∈ ((A ⊔ C : Subrepresentation (ρ.comp N.subtype)) : Set V) := by
    rw [hC.sup_eq_top]
    trivial
  rw [Subrepresentation.coe_sup] at hmem
  obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_add.1 hmem
  refine (Submodule.ne_bot_iff _).2 ⟨c, fun n ↦ ?_, fun hc0 ↦ hmA ?_⟩
  · have hA : (ρ.comp N.subtype) n c - c ∈ A.toSubmodule := by
      have := A.toSubmodule.sub_mem (hfix n) (A.toSubmodule.sub_mem
        (A.apply_mem_toSubmodule n ha) ha)
      convert this using 1
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, map_add]
      abel
    have hC' : (ρ.comp N.subtype) n c - c ∈ C :=
      C.toSubmodule.sub_mem (C.apply_mem_toSubmodule n hc) hc
    have h0 : (ρ.comp N.subtype) n c - c ∈ A ⊓ C := ⟨hA, hC'⟩
    rw [hC.inf_eq_bot] at h0
    exact sub_eq_zero.1 h0
  · rw [hc0, add_zero]
    exact ha

end Representation
