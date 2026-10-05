/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Topological Krull dimension: open covers and complements of dense opens

In a quasi-sober `T₀` space, the coheight of a point is bounded by the topological Krull
dimension, and the topological Krull dimension is bounded by any common bound on the
dimensions of the members of an open cover. In an irreducible `T₀` space of dimension at most
one, every point outside a nonempty open subset is closed; if the space is moreover quasi-sober
and noetherian, there are only finitely many such points.

## Main statements

- `coheight_le_topologicalKrullDim`: the coheight of a point for the specialization order is
  at most the topological Krull dimension.
- `topologicalKrullDim_le_of_iSup_eq_top`: the topological Krull dimension is at most any
  common bound on the dimensions of the members of an open cover.
- `IsOpen.finite_compl_of_topologicalKrullDim_le_one`: the complement of a nonempty open subset
  is finite.
- `IsOpen.isClosed_singleton_of_mem_compl`: each point of that complement is closed.
- `topologicalKrullDim_le_of_specializingMap`, `topologicalKrullDim_le_of_continuous`: comparison
  of the dimensions of two sober spaces along a specializing surjection, respectively along a
  continuous map that is injective on specializations.
-/

@[expose] public section

open Topology TopologicalSpace Order

attribute [local instance] specializationOrder in
/-- In a quasi-sober `T₀` space, the coheight of a point for the specialization order is at
most the topological Krull dimension. -/
theorem coheight_le_topologicalKrullDim {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] (x : X) : (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  rw [← coheight_orderIso irreducibleSetEquivPoints.symm]
  exact coheight_le_krullDim _

attribute [local instance] specializationOrder in
/-- The topological Krull dimension of a quasi-sober `T₀` space is bounded by any common
bound on the dimensions of the members of an open cover. -/
theorem topologicalKrullDim_le_of_iSup_eq_top {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {ι : Type*} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) (n : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (U i) ≤ n) : topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, krullDim_eq_iSup_coheight]
  refine iSup_le fun Z ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ (irreducibleSetEquivPoints Z)))
  have := (U i).isOpenEmbedding'.quasiSober
  rw [← coheight_orderIso irreducibleSetEquivPoints Z]
  exact (congrArg _ ((U i).isOpenEmbedding'.coheight_eq (x := (⟨_, hi⟩ : U i)))).trans_le
    ((coheight_le_topologicalKrullDim _).trans (h i))

section

variable {X : Type*} [TopologicalSpace X] [IrreducibleSpace X] [T0Space X]

/-- In an irreducible `T₀` space of dimension at most one, every point outside a
nonempty open subset `U` is closed: it is not the generic point, so a proper specialization of it
would give a chain of three irreducible closed subsets. -/
theorem IsOpen.isClosed_singleton_of_mem_compl (h : topologicalKrullDim X ≤ 1) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) {x : X} (hx : x ∉ U) : IsClosed {x} := by
  obtain ⟨u, hu⟩ := hne
  by_contra hcl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure {x}, y ≠ x := by
    by_contra! H
    exact hcl (closure_subset_iff_isClosed.mp fun y hy ↦ H y hy)
  let Y : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h₁ : Y < Z := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {x} from
      closure_minimal (by simpa using hy) isClosed_closure) fun h ↦ hyx ?_
    exact (inseparable_iff_closure_eq.mpr congr(($h : Set X))).eq
  have h₂ : Z < T := by
    refine lt_of_le_of_ne (show closure {x} ⊆ Set.univ from Set.subset_univ _) fun h ↦ hx ?_
    have hu' : u ∈ closure ({x} : Set X) := by
      rw [show closure ({x} : Set X) = Set.univ from congr(($h : Set X))]; trivial
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hu' U hU hu
    rwa [Set.mem_singleton_iff.mp hz] at hzU
  let q₁ : LTSeries (IrreducibleCloseds X) := (RelSeries.singleton _ Y).snoc Z h₁
  let q : LTSeries (IrreducibleCloseds X) :=
    q₁.snoc T (by rw [show q₁.last = Z from RelSeries.last_snoc _ _ _]; exact h₂)
  have hq : q.length = 2 := rfl
  have := Order.LTSeries.length_le_krullDim q
  rw [hq] at this
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := this.trans h
  exact absurd h2 (by decide)

/-- In an irreducible quasi-sober noetherian `T₀` space of dimension at most one, the complement
of a nonempty open subset is finite: it is a closed subset all of whose points are closed, so its
finitely many irreducible components are points. -/
theorem IsOpen.finite_compl_of_topologicalKrullDim_le_one [QuasiSober X] [NoetherianSpace X]
    (h : topologicalKrullDim X ≤ 1) {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    Uᶜ.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (hU.isClosed_singleton_of_mem_compl h hne hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z

end

section Map

open Order

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] [T0Space X]
  [QuasiSober Y] [T0Space Y]

attribute [local instance] specializationOrder

/-- The dimension of a quasi-sober `T₀` space is the Krull dimension of its points, ordered by
specialization. -/
theorem topologicalKrullDim_eq_krullDim_specializationOrder :
    topologicalKrullDim X = krullDim X :=
  krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- A surjective specializing map `f : X ⟶ Y` of quasi-sober `T₀` spaces satisfies
`dim Y ≤ dim X`: a chain of specializations in `Y` lifts to `X`, starting from its generic end.
-/
theorem topologicalKrullDim_le_of_specializingMap {f : X → Y} (hf : SpecializingMap f)
    (hsurj : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder, krullDim_eq_iSup_height,
    krullDim_eq_iSup_height]
  refine iSup_le fun y ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj y
  refine le_trans (WithBot.coe_le_coe.mpr ?_) (le_iSup (fun a : X ↦ (height a : WithBot ℕ∞)) x)
  suffices ∀ (n : ℕ) (p : LTSeries Y) (x : X), p.length = n → p.last = f x → (n : ℕ∞) ≤ height x
    from height_le fun p hp ↦ this _ p x rfl hp
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro p x hn hp
    have hlt : p.eraseLast.last < f x := hp ▸ p.eraseLast_last_rel_last (by omega)
    obtain ⟨x', hxx', hx'⟩ := hf hlt.le
    have hx'x : x' < x := lt_of_le_of_ne hxx' (by rintro rfl; exact hlt.ne hx'.symm)
    have := ih p.eraseLast x' (by simp [hn]) hx'.symm
    calc ((n + 1 : ℕ) : ℕ∞) = n + 1 := by push_cast; rfl
      _ ≤ height x' + 1 := by gcongr
      _ ≤ height x := height_add_one_le hx'x

/-- A continuous map `f : X ⟶ Y` of quasi-sober `T₀` spaces which identifies no two distinct
points `x ⤳ x'` satisfies `dim X ≤ dim Y`. -/
theorem topologicalKrullDim_le_of_continuous {f : X → Y} (hf : Continuous f)
    (hinj : ∀ x x', x ⤳ x' → f x = f x' → x = x') :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_krullDim_specializationOrder,
    topologicalKrullDim_eq_krullDim_specializationOrder]
  refine krullDim_le_of_strictMono f fun a b hab ↦ lt_of_le_of_ne (hab.le.map hf) fun h ↦ ?_
  exact hab.ne (hinj _ _ hab.le h.symm).symm

end Map
