/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The dimension of a sheaf of modules

The *dimension* of a sheaf of modules `F` on a scheme `X` is the Krull dimension of its support
`Supp F = {x | F_x ≠ 0}`, taken with the subspace topology. It is the quantity Snapper's
theorem is proved by induction on, and this file provides the two facts such an induction
consumes: the base case, that `dim F = ⊥` exactly when `F = 0`, and the inductive step, that a
closed subset of `Supp F` containing no irreducible component of `Supp F` has strictly smaller
dimension.

The base case is the statement that a sheaf of modules all of whose stalks vanish is zero: a
section of a sheaf with vanishing germs everywhere is zero, so all the groups of sections
vanish.

The inductive step is purely topological, and is proved in the mirror file
`WeilConjectures.Mathlib.Topology.KrullDimension` as
`topologicalKrullDim_lt_of_forall_maximal`. The finiteness of `dim X` that turns
`dim Z + 1 ≤ dim Supp F` into a strict inequality is `exists_topologicalKrullDim_le`, which is
where the hypothesis that `X` is quasi-compact of finite type over a field comes from.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.dim`: the dimension `dim F` of a sheaf of modules, the
  Krull dimension of its support.

## Main results

- `AlgebraicGeometry.Scheme.Modules.isZero_iff_support_eq_empty` and
  `AlgebraicGeometry.Scheme.Modules.dim_eq_bot_iff`: **the base case**, `dim F = ⊥` if and only
  if `Supp F = ∅` if and only if `F = 0`.
- `AlgebraicGeometry.Scheme.Modules.topologicalKrullDim_lt_dim` and
  `AlgebraicGeometry.Scheme.Modules.dim_lt_dim`: **the inductive step**, a closed subset of
  `Supp F` no maximal irreducible subset of which it contains has dimension `< dim F`.

## Blueprint

This is the notation `dim F := dim Supp F` of the chapter `chap:deg` on the degree of the
isogeny, where the blueprint sets `dim ∅ = -1` so that `dim F = -1` exactly when `F = 0`; here
the empty support has dimension `⊥`, the bottom of `WithBot ℕ∞`. The two results are the two
steps of the induction on `dim F` in the proof of Snapper's theorem `thm:deg-snapper`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The dimension of a sheaf of modules `F`: the Krull dimension of its support
`{x | F_x ≠ 0}`, for the topology induced from the underlying space of the scheme. -/
noncomputable def dim : WithBot ℕ∞ := topologicalKrullDim F.support

lemma dim_def : F.dim = topologicalKrullDim F.support := rfl

/-- **A sheaf of modules with empty support is zero**: if all the stalks of `F` vanish then so
do all its groups of sections, because a section of a sheaf whose germs all vanish is zero. -/
theorem isZero_iff_support_eq_empty : IsZero F ↔ F.support = ∅ := by
  constructor
  · intro hF
    have hsec : ∀ U : X.Opens, Subsingleton Γ(F, U) := by
      intro U
      rw [← AddCommGrpCat.isZero_iff_subsingleton, IsZero.iff_id_eq_zero]
      have happ : (𝟙 F : F ⟶ F).app U = (0 : F ⟶ F).app U := by
        rw [hF.eq_of_src (𝟙 F) (0 : F ⟶ F)]
      simpa using happ
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
    rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hx
    refine hx ⟨fun a b ↦ ?_⟩
    obtain ⟨U, hxU, s, rfl⟩ := F.presheaf.exists_germ_eq a
    obtain ⟨V, hxV, t, rfl⟩ := F.presheaf.exists_germ_eq b
    have := hsec U
    have := hsec V
    rw [Subsingleton.elim s 0, Subsingleton.elim t 0, map_zero, map_zero]
  · intro hsupp
    have hst : ∀ x : X, Subsingleton (F.presheaf.stalk x) := by
      intro x
      rw [← not_nontrivial_iff_subsingleton]
      intro hx
      have hmem : x ∈ F.support := hx
      rw [hsupp] at hmem
      exact hmem
    rw [IsZero.iff_id_eq_zero]
    refine hom_ext _ _ fun U ↦ ?_
    rw [Hom.id_app, Hom.zero_app, ← IsZero.iff_id_eq_zero,
      AddCommGrpCat.isZero_iff_subsingleton]
    refine ⟨fun s t ↦ ?_⟩
    refine TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s t fun x hx ↦ ?_
    have := hst x
    exact Subsingleton.elim _ _

/-- **The base case of an induction on the dimension of a sheaf of modules**: the dimension of
`F` is `⊥` exactly when `F` is zero. -/
theorem dim_eq_bot_iff : F.dim = ⊥ ↔ IsZero F := by
  rw [dim_def, topologicalKrullDim_eq_bot_iff, Set.isEmpty_coe_sort,
    ← isZero_iff_support_eq_empty]

variable {F}

/-- **The inductive step of an induction on the dimension of a sheaf of modules**: a closed
subset `Z` of the support of `F` which contains no maximal irreducible subset of `Supp F` — in
a sober space, which contains the generic point of no irreducible component of `Supp F` — has
dimension strictly smaller than that of `F`. -/
theorem topologicalKrullDim_lt_dim {k : Type u} [Field k] [CompactSpace X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {Z : Set X} (hZ : IsClosed Z)
    (hZS : Z ⊆ F.support) (hF : F.support.Nonempty)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ F.support) T → ¬T ⊆ Z) :
    topologicalKrullDim Z < F.dim := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le f
  exact topologicalKrullDim_lt_of_forall_maximal hZS hZ hF
    ((topologicalKrullDim_subspace_le X F.support).trans hn) h

/-- The inductive step, for the dimension of a second sheaf of modules: if the support of `G` is
a closed subset of the support of `F` containing no maximal irreducible subset of `Supp F`, then
`dim G < dim F`. -/
theorem dim_lt_dim {k : Type u} [Field k] [CompactSpace X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] {G : X.Modules} (hZ : IsClosed G.support)
    (hZS : G.support ⊆ F.support) (hF : F.support.Nonempty)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ F.support) T → ¬T ⊆ G.support) :
    G.dim < F.dim :=
  topologicalKrullDim_lt_dim f hZ hZS hF h

end AlgebraicGeometry.Scheme.Modules
