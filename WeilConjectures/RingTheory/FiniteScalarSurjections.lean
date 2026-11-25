/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Lattice

/-! # Simultaneous finite free surjections after scalar extension

Given finitely many ring maps `A → B_j` along which a module `N` becomes finite, a single finite
free `A`-module maps to `N` so that every scalar extension of this map is surjective.

## Main results

* `ModuleCat.exists_finiteFree_scalar_surjections`

## Implementation details

For each `j`, the second tensor factors of finitely many generators of `B_j ⊗ N` span a finite
submodule `S_j` of `N` whose scalar extension surjects. A finite free module surjecting onto
`⨆ j, S_j` works for all `j`. No faithful flatness, unit-ideal hypothesis, or global finite
generation of `N` is needed, and the maps need not be localizations.

## References

* [Stacks, Tag 08EE] (finite family of generators in the proof)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem finite_submodule_scalar_surjective {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B) (N : ModuleCat.{u} A)
    (hfinite : Module.Finite B ((extendScalars f).obj N)) :
    ∃ S : Submodule A N, Module.Finite A S ∧
      Epi ((extendScalars f).map (ModuleCat.ofHom S.subtype)) := by
  algebraize [f]
  have : Module.Finite B (B ⊗[A] N) := hfinite
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := B) (M := B ⊗[A] N))
  obtain ⟨S, hS, hinc⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    (s : Set (B ⊗[A] N)) s.finite_toSet
  refine ⟨S, hS, ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  change Function.Surjective (S.subtype.baseChange B)
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  intro x hx
  obtain ⟨y, hy⟩ := hinc hx
  exact ⟨y, hy⟩

/-- Finitely many finite scalar extensions are covered by one finite free source.

If `B_j ⊗[A] N` is finite over `B_j` for finitely many ring maps `A → B_j`, there is a map
`A^k → N` whose scalar extension along each `A → B_j` is an epimorphism. -/
theorem exists_finiteFree_scalar_surjections (A : Type u) [CommRing A]
    (r : ℕ) (B : Fin r → Type u) [∀ j, CommRing (B j)]
    (f : ∀ j, A →+* B j) (N : ModuleCat.{u} A)
    (hfinite : ∀ j, Module.Finite (B j) ((extendScalars.{u, u, u} (f j)).obj N)) :
    ∃ k : ℕ, ∃ p : ModuleCat.of A (Fin k → A) ⟶ N,
      ∀ j, Epi ((extendScalars.{u, u, u} (f j)).map p) := by
  classical
  obtain ⟨S, hS, hep⟩ : ∃ S : Fin r → Submodule A N,
      (∀ j, Module.Finite A (S j)) ∧
      ∀ j, Epi ((extendScalars.{u, u, u} (f j)).map (ModuleCat.ofHom (S j).subtype)) := by
    choose S hS hep using fun j => finite_submodule_scalar_surjective (f j) N (hfinite j)
    exact ⟨S, hS, hep⟩
  let T : Submodule A N := ⨆ j, S j
  have hT : Module.Finite A T := by
    have : ∀ j, Module.Finite A (S j) := hS
    infer_instance
  obtain ⟨k, p, hp⟩ := Module.Finite.exists_fin' A T
  let p' : ModuleCat.of A (Fin k → A) ⟶ ModuleCat.of A T := ModuleCat.ofHom p
  have hpe : Epi p' := (ModuleCat.epi_iff_surjective p').2 hp
  refine ⟨k, p' ≫ ModuleCat.ofHom T.subtype, ?_⟩
  intro j
  have hepT : Epi ((extendScalars.{u, u, u} (f j)).map (ModuleCat.ofHom T.subtype)) := by
    let i : ModuleCat.of A (S j) ⟶ ModuleCat.of A T :=
      ModuleCat.ofHom (Submodule.inclusion (le_iSup S j))
    have hfac : i ≫ ModuleCat.ofHom T.subtype = ModuleCat.ofHom (S j).subtype := rfl
    have : Epi ((extendScalars.{u, u, u} (f j)).map i ≫
        (extendScalars.{u, u, u} (f j)).map (ModuleCat.ofHom T.subtype)) := by
      rw [← CategoryTheory.Functor.map_comp, hfac]
      exact hep j
    exact epi_of_epi ((extendScalars.{u, u, u} (f j)).map i) _
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end ModuleCat
