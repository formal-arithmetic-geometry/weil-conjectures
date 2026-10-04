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
# Complements of dense opens in spaces of dimension one

In an irreducible `T₀` space of dimension at most one, every point outside a nonempty open subset
is closed; if the space is moreover quasi-sober and noetherian, there are only finitely many such
points.

## Main statements

- `IsOpen.finite_compl_of_topologicalKrullDim_le_one`: the complement of a nonempty open subset
  is finite.
- `IsOpen.isClosed_singleton_of_mem_compl`: each point of that complement is closed.
- `topologicalKrullDim_le_of_specializingMap`, `topologicalKrullDim_le_of_continuous`: comparison
  of the dimensions of two sober spaces along a specializing surjection, respectively along a
  continuous map that is injective on specializations.
-/

@[expose] public section

open Topology TopologicalSpace

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

section Inducing

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An inducing map with closed range into an irreducible space of finite dimension, whose
source has the same dimension as the target, is surjective: otherwise a maximal chain of
irreducible closed subsets of the source, pushed forward and followed by the whole space, would be
longer than any chain of the target. -/
theorem Topology.IsInducing.surjective_of_topologicalKrullDim_eq [IrreducibleSpace X]
    {f : Y → X} (hf : IsInducing f) (hc : IsClosed (Set.range f))
    (hfin : topologicalKrullDim X ≠ ⊤) (h : topologicalKrullDim Y = topologicalKrullDim X) :
    Function.Surjective f := by
  by_contra hns
  have hne : Set.range f ≠ Set.univ := fun h ↦ hns (Set.range_eq_univ.1 h)
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hbot
  have hm' : m ≠ ⊤ := by
    rintro rfl
    exact hfin hm.symm
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hm'
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (show ((n : ℕ∞) : WithBot ℕ∞) ≤
    topologicalKrullDim Y from h ▸ hm.le)
  let top : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let l₀ := l.map _ (IrreducibleCloseds.map_strictMono_of_isInducing hf)
  have hlast : l₀.last < top := by
    refine lt_of_le_of_ne (fun x _ ↦ Set.mem_univ x) fun heq ↦ hne ?_
    refine Set.eq_univ_of_univ_subset ?_
    have : (top : Set X) ⊆ closure (f '' l.last) := by
      rw [← heq]
      rfl
    exact this.trans (closure_minimal (Set.image_subset_range _ _) hc)
  let l' := l₀.snoc top hlast
  have := Order.LTSeries.length_le_krullDim l'
  rw [show l'.length = n + 1 by simp [l', l₀, hl]] at this
  change _ ≤ topologicalKrullDim X at this
  rw [← hm] at this
  norm_cast at this
  omega

end Inducing
