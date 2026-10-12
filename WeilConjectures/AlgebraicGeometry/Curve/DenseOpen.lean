/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AssertionsTransfer
public import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforward
public import WeilConjectures.AlgebraicGeometry.Curve.ZeroDimensional
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.SixFunctors.OpenClosed.Exact

/-!
# Localisation of the eight curve assertions to a dense open

Let `X` be a reduced curve over an algebraically closed field `k` and `F` a constructible sheaf
of `𝐅_r`-modules on `X`. There is a dense open `j : U ⟶ X`, a finite disjoint union of
irreducible opens `U_a`, on which `F` is finite locally constant. Its complement `Z` is a finite
set of closed points, and the open–closed sequence `0 → j_! j^* F → F → i_* i^* F → 0` has a
third term which is the direct image of a sheaf on the zero-dimensional `Z`: it satisfies the
eight assertions and has no cohomology in positive degrees. Hence
`C(X, F) ↔ C(X, j_! j^* F)`, and splitting `j_! j^* F = ⨁_a j_{a,!} (F|_{U_a})`,
`C(X, F) ↔ ∀ a, C(X, j_{a,!} (F|_{U_a}))`.

## Main statements

- `Dense.exists_isIrreducible_pieces`: a dense open subset of a noetherian space contains a
  dense finite disjoint union of irreducible opens.
- `IsOpen.finite_compl_of_dense`: in a noetherian space of dimension at most one the
  complement of a dense open subset is a finite set of closed points.
- `AlgebraicGeometry.IsCurve.assertions_iff_lowerShriek_of_isFiniteLocallyConstant`: the
  dense-open reduction (blueprint `lemma-weil-pbc-curve-dense-open-reduction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology TopologicalSpace

/-! ### Topology -/

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- **Irreducible pieces of a dense open.** A dense open subset `U` of a noetherian space
contains finitely many pairwise disjoint irreducible open subsets `V a` with dense union: for
each irreducible component `C`, the points of `U` lying on no other component. -/
theorem Dense.exists_isIrreducible_pieces [NoetherianSpace X] {U : Set X} (hU : IsOpen U)
    (hd : Dense U) :
    ∃ (n : ℕ) (V : Fin n → Set X), (∀ a, IsOpen (V a)) ∧ (∀ a, V a ⊆ U) ∧
      Pairwise (fun a b ↦ Disjoint (V a) (V b)) ∧ (∀ a, IsIrreducible (V a)) ∧
      Dense (⋃ a, V a) := by
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := X)
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  let e := Finite.equivFin (irreducibleComponents X)
  let C : Fin (Nat.card (irreducibleComponents X)) → Set X := fun a ↦ (e.symm a).1
  have hC (a) : C a ∈ irreducibleComponents X := (e.symm a).2
  have hCinj : Function.Injective C := fun a b h ↦ e.symm.injective (Subtype.ext h)
  let O a := (⋃₀ (irreducibleComponents X \ {C a}))ᶜ
  have hO (a) : IsOpen (O a) := by
    change IsOpen (⋃₀ _)ᶜ
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hOC (a) : closure (O a) = C a :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfin _ (hC a)
  have hOsub (a) : O a ⊆ C a := (hOC a) ▸ subset_closure
  have hOne (a) : (O a).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hOC a
    rw [h, closure_empty] at this
    exact (hC a).1.nonempty.ne_empty this.symm
  refine ⟨_, fun a ↦ U ∩ O a, fun a ↦ hU.inter (hO a), fun a ↦ Set.inter_subset_left,
    fun a b hab ↦ ?_, fun a ↦ ?_, ?_⟩
  · refine Set.disjoint_left.2 fun x hxa hxb ↦ hxb.2 ?_
    exact Set.mem_sUnion_of_mem (hOsub a hxa.2) ⟨hC a, fun h ↦ hab (hCinj h)⟩
  · exact (hC a).1.2.subset_irreducible
      (by rw [Set.inter_comm]; exact hd.inter_open_nonempty _ (hO a) (hOne a))
      (hU.inter (hO a)) subset_rfl (Set.inter_subset_right.trans (hOsub a))
  · refine dense_iff_closure_eq.2 (Set.eq_univ_of_forall fun x ↦ ?_)
    let a := e ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
    have hx : x ∈ C a := by
      simp only [C, a, Equiv.symm_apply_apply]
      exact mem_irreducibleComponent
    have hne : (C a ∩ (U ∩ O a)).Nonempty := by
      obtain ⟨y, hy⟩ := hd.inter_open_nonempty _ (hO a) (hOne a)
      exact ⟨y, hOsub a hy.1, hy.2, hy.1⟩
    refine closure_mono (Set.subset_iUnion (fun a ↦ U ∩ O a) a) ?_
    exact closure_mono Set.inter_subset_right
      (subset_closure_inter_of_isPreirreducible_of_isOpen (hC a).1.2 (hU.inter (hO a)) hne hx)

variable [QuasiSober X] [T0Space X]

/-- In a noetherian `T₀` space of dimension at most one, every point outside a dense open
subset `U` is closed: a proper specialization of it, the point itself and the generic point of
an irreducible component through it (which meets `U`) would form a chain of length two. -/
omit [QuasiSober X] in
theorem IsOpen.isClosed_singleton_of_dense [NoetherianSpace X] (h : topologicalKrullDim X ≤ 1)
    {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : x ∉ U) : IsClosed {x} := by
  by_contra hcl
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ closure {x}, y ≠ x := by
    by_contra! H
    exact hcl (closure_subset_iff_isClosed.mp fun y hy ↦ H y hy)
  have hT := irreducibleComponent_mem_irreducibleComponents x
  let Y : IrreducibleCloseds X := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X :=
    ⟨irreducibleComponent x, isIrreducible_irreducibleComponent, isClosed_irreducibleComponent⟩
  have h₁ : Y < Z := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {x} from
      closure_minimal (by simpa using hy) isClosed_closure) fun h ↦ hyx ?_
    exact (inseparable_iff_closure_eq.mpr congr(($h : Set X))).eq
  have h₂ : Z < T := by
    refine lt_of_le_of_ne (show closure {x} ⊆ irreducibleComponent x from
      closure_minimal (by simpa using mem_irreducibleComponent) isClosed_irreducibleComponent)
      fun h ↦ ?_
    obtain ⟨o, ho, hne, hoT⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hT
    obtain ⟨u, huo, huU⟩ := hd.inter_open_nonempty o ho hne
    have hu : u ∈ closure ({x} : Set X) := by
      rw [show closure ({x} : Set X) = irreducibleComponent x from congr(($h : Set X))]
      exact hoT huo
    have : closure ({x} : Set X) ⊆ Uᶜ :=
      closure_minimal (by simpa using hx) hU.isClosed_compl
    exact this hu huU
  let q₁ : LTSeries (IrreducibleCloseds X) := (RelSeries.singleton _ Y).snoc Z h₁
  let q : LTSeries (IrreducibleCloseds X) :=
    q₁.snoc T (by rw [show q₁.last = Z from RelSeries.last_snoc _ _ _]; exact h₂)
  have hq : q.length = 2 := rfl
  have := Order.LTSeries.length_le_krullDim q
  rw [hq] at this
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := this.trans h
  exact absurd h2 (by decide)

/-- In a quasi-sober noetherian `T₀` space of dimension at most one, the complement of a dense
open subset is finite. -/
theorem IsOpen.finite_compl_of_dense [NoetherianSpace X] (h : topologicalKrullDim X ≤ 1)
    {U : Set X} (hU : IsOpen U) (hd : Dense U) : Uᶜ.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    hU.isClosed_compl
  have key : ∀ t ∈ S, ∃ z, t = {z} := by
    intro t ht
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
    have hzU : z ∉ U := by
      have : z ∈ Uᶜ := hS ▸ Set.mem_sUnion_of_mem hz.mem ht
      exact this
    exact ⟨z, by rw [← hz.def, (hU.isClosed_singleton_of_dense h hd hzU).closure_eq]⟩
  rw [hS]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨z, rfl⟩ := key t ht
  exact Set.finite_singleton z

/-- In a quasi-sober noetherian `T₀` space of dimension at most one, the complement of a dense
open subset has dimension at most zero. -/
theorem IsOpen.topologicalKrullDim_compl_le_zero [NoetherianSpace X]
    (h : topologicalKrullDim X ≤ 1) {U : Set X} (hU : IsOpen U) (hd : Dense U) :
    topologicalKrullDim ↥Uᶜ ≤ 0 := by
  have : Finite ↥Uᶜ := (hU.finite_compl_of_dense h hd).to_subtype
  have : T1Space ↥Uᶜ := ⟨fun x ↦ isClosed_induced_iff.2
    ⟨{x.1}, hU.isClosed_singleton_of_dense h hd x.2, by ext y; simp [Subtype.ext_iff]⟩⟩
  exact topologicalKrullDim_zero_of_discreteTopology _

end Topology
