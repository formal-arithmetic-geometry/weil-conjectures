/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.Topology.Sober

/-!
# The dimension of a sheaf of modules

The *dimension* of a sheaf of modules `F` on a scheme `X` is the Krull dimension of its support
`Supp F = {x | F_x ≠ 0}`, taken with the subspace topology. It is the quantity Snapper's
theorem is proved by induction on, and this file provides the two facts such an induction
consumes: the base case, that `dim F = ⊥` exactly when `F = 0`, and the inductive step, that a
sheaf `G` whose support is a closed subset of `Supp F` containing the generic point of no
irreducible component of `Supp F` has `dim G + 1 ≤ dim F`, hence `dim G < dim F` as soon as
`dim F` is finite.

The inductive step is purely topological: appending an irreducible component of `Supp F` to a
chain of irreducible closed subsets of `Supp G` lengthens it by one, which is
`topologicalKrullDim_add_one_le_of_forall_maximal`. What turns the maximal irreducible subsets
appearing there into the generic points of the irreducible components — the form in which the
hypothesis is available in practice, and the form Snapper's induction produces — is
`exists_mem_minimal_specializes_of_maximal_isIrreducible`; a point is a generic point of an
irreducible component of `Supp F` exactly when it is minimal for specialization in `Supp F`,
which is also how `AlgebraicGeometry.Scheme.Modules.isAssociatedPoint_of_minimal_mem_support`
phrases it.

The finiteness of `dim F` that turns `dim G + 1 ≤ dim F` into a strict inequality is recorded
separately, as `AlgebraicGeometry.Scheme.Modules.supportDim_ne_top`, so that the inductive step
itself is free of hypotheses on the scheme.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.supportDim`: the dimension `dim F` of a sheaf of modules,
  the Krull dimension of its support. It is named after its algebraic counterpart
  `Module.supportDim`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.supportDim_eq_bot_iff`: `dim F = ⊥` if and only if `F` is a
  zero object. This is the base case of the induction.
- `AlgebraicGeometry.Scheme.Modules.supportDim_add_one_le_supportDim_of_forall_minimal` and its
  strict form `AlgebraicGeometry.Scheme.Modules.supportDim_lt_supportDim_of_forall_minimal`: if
  `Supp G` is a closed subset of the closed set `Supp F` containing no point of `Supp F`
  minimal for specialization, then `dim G + 1 ≤ dim F`, and `dim G < dim F` when `dim F ≠ ⊤`.
  This is the inductive step.

## Blueprint

This is the notation `dim F := dim Supp F` of the chapter `chap:deg` on the degree of the
isogeny, where the blueprint sets `dim ∅ = -1` so that `dim F = -1` exactly when `F = 0`; here
the empty support has dimension `⊥`, the bottom of `WithBot ℕ∞`. The two results are the two
steps of the induction on `dim F` in the proof of Snapper's theorem `thm:deg-snapper`:
`def:deg-dim`, `lem:deg-dim-eq-bot` and `lem:deg-dim-lt`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The dimension of a sheaf of modules `F`: the Krull dimension of its support
`{x | F_x ≠ 0}`, for the topology induced from the underlying space of the scheme. -/
noncomputable def supportDim : WithBot ℕ∞ := topologicalKrullDim F.support

lemma supportDim_def : F.supportDim = topologicalKrullDim F.support := rfl

/-- The dimension of a sheaf of modules is `⊥` if and only if the sheaf is a zero object. -/
theorem supportDim_eq_bot_iff : F.supportDim = ⊥ ↔ IsZero F := by
  rw [supportDim_def, topologicalKrullDim_eq_bot_iff, Set.isEmpty_coe_sort,
    support_eq_empty_iff_isZero]

/-- A sheaf of modules on a quasi-compact scheme of finite type over a field has finite
dimension, because such a scheme does. -/
theorem supportDim_ne_top {k : Type u} [Field k] [CompactSpace X] (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] : F.supportDim ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le f
  exact ne_top_of_le_ne_top (ENat.WithBot.natCast_ne_top n)
    ((topologicalKrullDim_subspace_le X F.support).trans hn)

variable {F}

/-- The inductive step, in terms of maximal irreducible subsets: if the support of `G` is a
closed subset of the support of `F` containing no maximal irreducible subset of `Supp F`, then
`dim G + 1 ≤ dim F`. -/
theorem supportDim_add_one_le_supportDim_of_forall_maximal {G : X.Modules}
    (hGF : G.support ⊆ F.support) (hG : IsClosed G.support)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ F.support) T → ¬T ⊆ G.support) :
    G.supportDim + 1 ≤ F.supportDim :=
  topologicalKrullDim_add_one_le_of_forall_maximal hGF (hG.preimage continuous_subtype_val) h

/-- The strict form of `supportDim_add_one_le_supportDim_of_forall_maximal`, for a sheaf `F`
with nonempty support of finite dimension. -/
theorem supportDim_lt_supportDim_of_forall_maximal {G : X.Modules}
    (hGF : G.support ⊆ F.support) (hG : IsClosed G.support) (hFne : F.support.Nonempty)
    (hfin : F.supportDim ≠ ⊤)
    (h : ∀ T, Maximal (fun W ↦ IsIrreducible W ∧ W ⊆ F.support) T → ¬T ⊆ G.support) :
    G.supportDim < F.supportDim :=
  topologicalKrullDim_lt_of_forall_maximal hGF (hG.preimage continuous_subtype_val) hFne hfin h

/-- **The inductive step of an induction on the dimension of a sheaf of modules**: if `Supp F`
is closed and `Supp G` is a closed subset of it containing no point of `Supp F` minimal for
specialization — that is, no generic point of an irreducible component of `Supp F` — then
`dim G + 1 ≤ dim F`. -/
theorem supportDim_add_one_le_supportDim_of_forall_minimal {G : X.Modules}
    (hF : IsClosed F.support) (hGF : G.support ⊆ F.support) (hG : IsClosed G.support)
    (h : ∀ x ∈ F.support, (∀ y ∈ F.support, y ⤳ x → y = x) → x ∉ G.support) :
    G.supportDim + 1 ≤ F.supportDim := by
  refine supportDim_add_one_le_supportDim_of_forall_maximal hGF hG fun T hT hTG ↦ ?_
  obtain ⟨x, hxT, hxmin⟩ := exists_mem_minimal_specializes_of_maximal_isIrreducible hF hT
  exact h x (hT.1.2 hxT) hxmin (hTG hxT)

/-- The strict form of `supportDim_add_one_le_supportDim_of_forall_minimal`, for a sheaf `F`
with nonempty support of finite dimension. -/
theorem supportDim_lt_supportDim_of_forall_minimal {G : X.Modules} (hF : IsClosed F.support)
    (hGF : G.support ⊆ F.support) (hG : IsClosed G.support) (hFne : F.support.Nonempty)
    (hfin : F.supportDim ≠ ⊤)
    (h : ∀ x ∈ F.support, (∀ y ∈ F.support, y ⤳ x → y = x) → x ∉ G.support) :
    G.supportDim < F.supportDim := by
  refine supportDim_lt_supportDim_of_forall_maximal hGF hG hFne hfin fun T hT hTG ↦ ?_
  obtain ⟨x, hxT, hxmin⟩ := exists_mem_minimal_specializes_of_maximal_isIrreducible hF hT
  exact h x (hT.1.2 hxT) hxmin (hTG hxT)

end AlgebraicGeometry.Scheme.Modules
