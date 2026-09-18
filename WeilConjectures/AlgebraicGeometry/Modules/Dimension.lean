/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.Data.ENat.Basic
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

- `AlgebraicGeometry.Scheme.Modules.support_eq_empty_iff_isZero`: a sheaf of modules has empty
  support if and only if it is a zero object.
- `AlgebraicGeometry.Scheme.Modules.isClosed_support`: the support of a coherent sheaf of
  modules is closed.
- `AlgebraicGeometry.Scheme.Modules.supportDim_eq_bot_iff`: `dim F = ⊥` if and only if `F` is a
  zero object, and its consequence
  `AlgebraicGeometry.Scheme.Modules.isZero_of_supportDim_lt_zero`. This is the base case of the
  induction.
- `AlgebraicGeometry.Scheme.Modules.supportDim_add_one_le_supportDim_of_forall_minimal` and its
  strict form `AlgebraicGeometry.Scheme.Modules.supportDim_lt_supportDim_of_forall_minimal`: if
  `Supp G` is a subset of `Supp F` containing no point of `Supp F` minimal for specialization,
  then `dim G + 1 ≤ dim F`, and `dim G < dim F` when `dim F ≠ ⊤`. This is the inductive step.

## Blueprint

This is the notation `dim F := dim Supp F` of the chapter `chap:deg` on the degree of the
isogeny, where the blueprint sets `dim ∅ = -1` so that `dim F = -1` exactly when `F = 0`; here
the empty support has dimension `⊥`, the bottom of `WithBot ℕ∞`. The two results are the two
steps of the induction on `dim F` in the proof of Snapper's theorem `thm:deg-snapper`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- **A sheaf of modules on a scheme has empty support if and only if it is a zero object**,
that is, if and only if all of its stalks vanish.

Mathlib's `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` is the same statement for a sheaf of
abelian groups. Using it here would mean transporting it along the forgetful functor from
`X.Modules` to `TopCat.Sheaf AddCommGrpCat X` and checking that the latter reflects zero objects;
the direct argument below is shorter. -/
theorem support_eq_empty_iff_isZero : F.support = ∅ ↔ IsZero F := by
  constructor
  · intro hsupp
    -- a section of a sheaf all of whose germs vanish is zero
    have hst (x : X) : Subsingleton (F.presheaf.stalk x) :=
      not_nontrivial_iff_subsingleton.1 fun hx ↦ by
        simpa [hsupp] using (mem_support_iff F x).2 hx
    rw [IsZero.iff_id_eq_zero]
    refine hom_ext _ _ fun U ↦ ?_
    rw [Hom.id_app, Hom.zero_app, ← IsZero.iff_id_eq_zero,
      AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun s t ↦ TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s t fun x _ ↦
      Subsingleton.elim _ _⟩
  · intro hF
    have hsec (U : X.Opens) : Subsingleton Γ(F, U) := by
      rw [← AddCommGrpCat.isZero_iff_subsingleton, IsZero.iff_id_eq_zero]
      simpa using congrArg (fun φ : F ⟶ F ↦ φ.app U) (hF.eq_of_src (𝟙 F) 0)
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_
    rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hx
    refine hx ⟨fun a b ↦ ?_⟩
    obtain ⟨U, hxU, s, rfl⟩ := F.presheaf.exists_germ_eq a
    obtain ⟨V, hxV, t, rfl⟩ := F.presheaf.exists_germ_eq b
    have := hsec U
    have := hsec V
    rw [Subsingleton.elim s 0, Subsingleton.elim t 0, map_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- **The support of a coherent sheaf of modules is closed.** -/
theorem isClosed_support [F.IsCoherent] : IsClosed F.support := by
  -- on an affine open `U` the support meets `U` in the support of the `Γ(X, U)`-module
  -- `Γ(F, U)`, which is the zero locus of its annihilator because that module is finite
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Module.Finite Γ(X, U) Γ(F, U) := finite_sections F ⟨U, hU⟩
  have hclosed : IsClosed (Module.support Γ(X, U) Γ(F, U)) := by
    rw [Module.support_eq_zeroLocus]
    exact PrimeSpectrum.isClosed_zeroLocus _
  have hinj : Function.Injective hU.fromSpec.base := hU.fromSpec.isOpenEmbedding.injective
  refine ⟨hU.fromSpec.base '' (Module.support Γ(X, U) Γ(F, U))ᶜ, ?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hmem : hU.fromSpec p ∈ U := by
      have hr : hU.fromSpec p ∈ Set.range hU.fromSpec.base := Set.mem_range_self _
      rwa [hU.range_fromSpec] at hr
    have hpio : hU.primeIdealOf ⟨hU.fromSpec p, hmem⟩ = p :=
      hinj (hU.fromSpec_primeIdealOf ⟨_, hmem⟩)
    simp only [Set.mem_compl_iff]
    rw [mem_support_iff_mem_module_support F hU ⟨_, hmem⟩, hpio]
    exact hp
  · exact hU.fromSpec.isOpenEmbedding.isOpenMap _ hclosed.isOpen_compl
  · refine ⟨hU.primeIdealOf ⟨x, hxU⟩, ?_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
    simpa [← mem_support_iff_mem_module_support F hU ⟨x, hxU⟩] using hx

/-- The dimension of a sheaf of modules `F`: the Krull dimension of its support
`{x | F_x ≠ 0}`, for the topology induced from the underlying space of the scheme. -/
noncomputable def supportDim : WithBot ℕ∞ := topologicalKrullDim F.support

lemma supportDim_def : F.supportDim = topologicalKrullDim F.support := rfl

/-- The dimension of a sheaf of modules is `⊥` if and only if the sheaf is a zero object. -/
theorem supportDim_eq_bot_iff : F.supportDim = ⊥ ↔ IsZero F := by
  rw [supportDim_def, topologicalKrullDim_eq_bot_iff, Set.isEmpty_coe_sort,
    support_eq_empty_iff_isZero]

/-- A sheaf of modules whose dimension is below `0` is a zero object: nothing but `⊥` lies below
`0` in `WithBot ℕ∞`. This is the form the base case of an induction on `dim F` is used in. -/
theorem isZero_of_supportDim_lt_zero (h : F.supportDim < ((0 : ℕ) : WithBot ℕ∞)) : IsZero F :=
  (supportDim_eq_bot_iff F).1 (ENat.WithBot.lt_natCast_zero_iff.1 h)

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

/-- **The inductive step of an induction on the dimension of a sheaf of modules**: if `Supp G`
is a subset of `Supp F` containing no point of `Supp F` minimal for specialization — that is,
no generic point of an irreducible component of `Supp F` — then `dim G + 1 ≤ dim F`.

Closedness of the two supports, which the topological statement
`supportDim_add_one_le_supportDim_of_forall_maximal` takes as a hypothesis, is automatic for
coherent sheaves by `AlgebraicGeometry.Scheme.Modules.isClosed_support`. -/
theorem supportDim_add_one_le_supportDim_of_forall_minimal [F.IsCoherent] {G : X.Modules}
    [G.IsCoherent] (hGF : G.support ⊆ F.support)
    (h : ∀ x ∈ F.support, (∀ y ∈ F.support, y ⤳ x → y = x) → x ∉ G.support) :
    G.supportDim + 1 ≤ F.supportDim := by
  refine supportDim_add_one_le_supportDim_of_forall_maximal hGF (isClosed_support G)
    fun T hT hTG ↦ ?_
  obtain ⟨x, hxT, hxmin⟩ :=
    exists_mem_minimal_specializes_of_maximal_isIrreducible (isClosed_support F) hT
  exact h x (hT.1.2 hxT) hxmin (hTG hxT)

/-- The strict form of `supportDim_add_one_le_supportDim_of_forall_minimal`, for a sheaf `F`
with nonempty support of finite dimension. -/
theorem supportDim_lt_supportDim_of_forall_minimal [F.IsCoherent] {G : X.Modules}
    [G.IsCoherent] (hGF : G.support ⊆ F.support) (hFne : F.support.Nonempty)
    (hfin : F.supportDim ≠ ⊤)
    (h : ∀ x ∈ F.support, (∀ y ∈ F.support, y ⤳ x → y = x) → x ∉ G.support) :
    G.supportDim < F.supportDim := by
  refine supportDim_lt_supportDim_of_forall_maximal hGF (isClosed_support G) hFne hfin
    fun T hT hTG ↦ ?_
  obtain ⟨x, hxT, hxmin⟩ :=
    exists_mem_minimal_specializes_of_maximal_isIrreducible (isClosed_support F) hT
  exact h x (hT.1.2 hxT) hxmin (hTG hxT)

end AlgebraicGeometry.Scheme.Modules
