/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Order.JordanHolder
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Composition series of representations and the Jordan–Hölder theorem

A *composition series* of a representation `ρ` is a chain of subrepresentations
`0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ` in which every step is a covering, so that every composition
factor `F (i + 1) / F i` is irreducible (`Subrepresentation.isIrreducible_subquotient_iff`).
This file proves that a finite-dimensional representation has a composition series and the
Jordan–Hölder theorem for representations: any two composition series have the same length and,
up to a permutation, equivalent composition factors. It is deduced from Mathlib's Jordan–Hölder
theorem `CompositionSeries.jordan_holder` for modular lattices, the lattice of
subrepresentations being modular, and the second isomorphism theorem
`Subrepresentation.subquotientSupEquiv`.

## Main statements

- `Subrepresentation.exists_compositionSeries`: a finite-dimensional representation has a
  composition series.
- `Subrepresentation.exists_equiv_subquotient_of_compositionSeries`: the Jordan–Hölder theorem.
- `Subrepresentation.exists_equiv_of_isIrreducible_subquotient`: every irreducible subquotient
  is equivalent to a factor of any composition series.
- `Subrepresentation.factorMultiset_eq`: the multiset of an invariant of the composition factors
  does not depend on the composition series.
- `Subrepresentation.exists_compositionSeries_of_iSupIndep`: a decomposition into irreducible
  summands gives a composition series.
- `Subrepresentation.le_iSup_of_isInternal`: an irreducible subrepresentation of a direct sum of
  irreducibles lies in the sum of the summands equivalent to it (Schur).
-/

@[expose] public section

namespace Subrepresentation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The lattice of subrepresentations is modular, since it embeds into the lattice of
submodules, preserving `⊔` and `⊓`. -/
instance : IsModularLattice (Subrepresentation ρ) :=
  ⟨fun {x} y {z} hxz ↦ by
    rw [← toSubmodule_le_toSubmodule_iff, toSubmodule_inf, toSubmodule_sup, toSubmodule_sup,
      toSubmodule_inf]
    exact IsModularLattice.sup_inf_le_assoc_of_le _ hxz⟩

theorem mem_sup {x y : Subrepresentation ρ} {v : V} :
    v ∈ x ⊔ y ↔ ∃ a ∈ x, ∃ b ∈ y, a + b = v := by
  change v ∈ (x ⊔ y).toSubmodule ↔ _
  rw [toSubmodule_sup, Submodule.mem_sup]
  rfl

/-- The **second isomorphism theorem** for subrepresentations: `y / (x ⊓ y) ≅ (x ⊔ y) / x`. -/
noncomputable def subquotientSupEquiv (x y : Subrepresentation ρ) :
    (y.subquotient (x ⊓ y)).Equiv ((x ⊔ y).subquotient x) :=
  subquotientEquivOfIntertwiningMap (.id ρ) (fun v hv ↦
    mem_sup.2 ⟨0, x.toSubmodule.zero_mem, v, hv, zero_add v⟩)
    (fun _ _ hv ↦ (mem_inf.1 hv).1) (fun _ hvy hvx ↦ mem_inf.2 ⟨hvx, hvy⟩) fun w hw ↦ by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup.1 hw
      refine ⟨b, hb, ?_⟩
      rw [Representation.IntertwiningMap.id_apply, sub_add_cancel_right]
      exact x.toSubmodule.neg_mem ha

/-- A finite-dimensional representation has a composition series
`0 = F 0 ⋖ F 1 ⋖ ⋯ ⋖ F n = ρ`. -/
theorem exists_compositionSeries [FiniteDimensional k V] :
    ∃ (n : ℕ) (F : ℕ → Subrepresentation ρ), F 0 = ⊥ ∧ F n = ⊤ ∧
      ∀ i < n, F i ⋖ F (i + 1) := by
  have : WellFoundedLT (Subrepresentation ρ) :=
    ⟨Subrelation.wf (r := fun a b ↦ a.toSubmodule < b.toSubmodule) (fun h ↦ h)
      (InvImage.wf _ wellFounded_lt)⟩
  have : WellFoundedGT (Subrepresentation ρ) :=
    ⟨Subrelation.wf (r := fun a b ↦ b.toSubmodule < a.toSubmodule) (fun h ↦ h)
      (InvImage.wf _ wellFounded_gt)⟩
  obtain ⟨a, ha₀, n, hn, ha⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le (bot_le : (⊥ : Subrepresentation ρ) ≤ ⊤)
  exact ⟨n, a, ha₀, hn, ha⟩

/-- The composition series `0 = F 0 ⋖ ⋯ ⋖ F n = ρ` as a `CompositionSeries` of the modular
lattice of subrepresentations. -/
def toCompositionSeries {n : ℕ} {F : ℕ → Subrepresentation ρ} (hF : ∀ i < n, F i ⋖ F (i + 1)) :
    CompositionSeries (Subrepresentation ρ) where
  length := n
  toFun i := F i
  step i := hF i i.2

/-- The **Jordan–Hölder theorem** for representations: two composition series
`0 = F 0 ⋖ ⋯ ⋖ F n = ρ` and `0 = G 0 ⋖ ⋯ ⋖ G m = ρ` have, up to a bijection `e` of the index
sets, equivalent composition factors `F (i + 1) / F i ≅ G (e i + 1) / G (e i)`. -/
theorem exists_equiv_subquotient_of_compositionSeries {n m : ℕ} {F G : ℕ → Subrepresentation ρ}
    (hF0 : F 0 = ⊥) (hFn : F n = ⊤) (hF : ∀ i < n, F i ⋖ F (i + 1))
    (hG0 : G 0 = ⊥) (hGm : G m = ⊤) (hG : ∀ i < m, G i ⋖ G (i + 1)) :
    ∃ e : Fin n ≃ Fin m, ∀ i : Fin n,
      Nonempty (((F (i + 1)).subquotient (F i)).Equiv ((G (e i + 1)).subquotient (G (e i)))) := by
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder (toCompositionSeries hF)
    (toCompositionSeries hG) (by simp [toCompositionSeries, RelSeries.head, hF0, hG0])
    (by simp [toCompositionSeries, RelSeries.last, hFn, hGm])
  refine ⟨e, fun i ↦ ?_⟩
  have h := he i
  simp only [toCompositionSeries, Fin.val_castSucc, Fin.val_succ] at h
  exact JordanHolderLattice.Iso.rel
    (fun a b ↦ Nonempty (((a.2).subquotient a.1).Equiv ((b.2).subquotient b.1)))
    (fun {_} ↦ ⟨Representation.Equiv.refl _⟩) (fun {_ _} ⟨e⟩ ↦ ⟨e.symm⟩)
    (fun {_ _ _} ⟨e₁⟩ ⟨e₂⟩ ↦ ⟨e₁.trans e₂⟩)
    (fun {x y} _ ↦ ⟨(subquotientSupEquiv x y).symm⟩) h

/-- Every irreducible subquotient `S / U` of a finite-dimensional representation is equivalent
to a composition factor `F (i + 1) / F i` of any composition series `F` (Jordan–Hölder). -/
theorem exists_equiv_of_isIrreducible_subquotient [FiniteDimensional k V] {n : ℕ}
    {F : ℕ → Subrepresentation ρ} (hF0 : F 0 = ⊥) (hFn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) {U S : Subrepresentation ρ}
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ i : Fin n, Nonempty ((S.subquotient U).Equiv ((F (i + 1)).subquotient (F i))) := by
  have e₀ := subquotientInfEquiv U S
  have hcov : U ⊓ S ⋖ S := (isIrreducible_subquotient_iff inf_le_right).1
    (e₀.isIrreducible_iff.2 hirr)
  obtain ⟨m, G, i₀, hG0, hGm, hG, hi₀, hGi₀, hGi₀'⟩ := exists_covBy_chain hcov
  obtain ⟨e, he⟩ := exists_equiv_subquotient_of_compositionSeries hG0 hGm hG hF0 hFn hF
  obtain ⟨e₁⟩ := he ⟨i₀, hi₀⟩
  refine ⟨e ⟨i₀, hi₀⟩, ⟨e₀.symm.trans ?_⟩⟩
  rw [hGi₀, hGi₀'] at e₁
  exact e₁

/-- **Jordan–Hölder for invariants of composition factors**: if `f N M` only depends on the
composition factor `M / N` up to equivalence, then the multiset of the values of `f` on the
factors of a composition series does not depend on the series. -/
theorem map_univ_eq_of_compositionSeries {α : Type*}
    (f : Subrepresentation ρ → Subrepresentation ρ → α)
    (hf : ∀ N M N' M' : Subrepresentation ρ,
      Nonempty ((M.subquotient N).Equiv (M'.subquotient N')) → f N M = f N' M')
    {n m : ℕ} {F G : ℕ → Subrepresentation ρ}
    (hF0 : F 0 = ⊥) (hFn : F n = ⊤) (hF : ∀ i < n, F i ⋖ F (i + 1))
    (hG0 : G 0 = ⊥) (hGm : G m = ⊤) (hG : ∀ i < m, G i ⋖ G (i + 1)) :
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n ↦ f (F i) (F ((i : ℕ) + 1))) =
      (Finset.univ : Finset (Fin m)).val.map (fun i : Fin m ↦ f (G i) (G ((i : ℕ) + 1))) := by
  obtain ⟨e, he⟩ := exists_equiv_subquotient_of_compositionSeries hF0 hFn hF hG0 hGm hG
  rw [← Multiset.map_univ_val_equiv e, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ ↦ hf _ _ _ _ (he i)

/-- The multiset of values of `f` on the composition factors `F (i + 1) / F i` of a chosen
composition series of a finite-dimensional representation. When `f N M` only depends on the
factor `M / N` up to equivalence, it can be computed from any composition series
(`Subrepresentation.factorMultiset_eq`). -/
noncomputable def factorMultiset (ρ : Representation k G V) [FiniteDimensional k V] {α : Type*}
    (f : Subrepresentation ρ → Subrepresentation ρ → α) : Multiset α :=
  (Finset.univ : Finset (Fin (exists_compositionSeries (ρ := ρ)).choose)).val.map
    fun i : Fin (exists_compositionSeries (ρ := ρ)).choose ↦
      f ((exists_compositionSeries (ρ := ρ)).choose_spec.choose i)
        ((exists_compositionSeries (ρ := ρ)).choose_spec.choose ((i : ℕ) + 1))

/-- `Subrepresentation.factorMultiset` can be computed from any composition series, by the
Jordan–Hölder theorem. -/
theorem factorMultiset_eq [FiniteDimensional k V] {α : Type*}
    (f : Subrepresentation ρ → Subrepresentation ρ → α)
    (hf : ∀ N M N' M' : Subrepresentation ρ,
      Nonempty ((M.subquotient N).Equiv (M'.subquotient N')) → f N M = f N' M')
    {n : ℕ} {F : ℕ → Subrepresentation ρ} (hF0 : F 0 = ⊥) (hFn : F n = ⊤)
    (hF : ∀ i < n, F i ⋖ F (i + 1)) :
    factorMultiset ρ f =
      (Finset.univ : Finset (Fin n)).val.map fun i : Fin n ↦ f (F i) (F ((i : ℕ) + 1)) :=
  have h := (exists_compositionSeries (ρ := ρ)).choose_spec.choose_spec
  map_univ_eq_of_compositionSeries f hf h.1 h.2.1 h.2.2 hF0 hFn hF

/-- Subquotients can be transported along an equivalence of representations `e : ρ ≅ σ`: every
subquotient `S / U` of `σ` is equivalent to a subquotient `S' / U'` of `ρ`. -/
theorem exists_subquotient_equiv_of_equiv {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k G V'} (e : ρ.Equiv σ) (U S : Subrepresentation σ) :
    ∃ U' S' : Subrepresentation ρ, Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) :=
  ⟨_, _, ⟨(subquotientEquiv e.symm S U).symm⟩⟩

/-- A subquotient `S' / U'` of a subquotient `M / N` of `ρ` is equivalent to a subquotient of
`ρ`: its preimage in `M`, viewed inside `V`. -/
theorem exists_subquotient_equiv_of_subquotient {M N : Subrepresentation ρ}
    (U' S' : Subrepresentation (M.subquotient N)) :
    ∃ U S : Subrepresentation ρ, Nonempty ((S.subquotient U).Equiv (S'.subquotient U')) := by
  let q : M.toRepresentation.IntertwiningMap (M.subquotient N) := ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
  let ι : M.toRepresentation.IntertwiningMap ρ := ⟨Submodule.subtype _, fun _ ↦ rfl⟩
  have hι : Function.Injective ι := Submodule.injective_subtype _
  let e₁ := subquotientComapEquiv q (Submodule.mkQ_surjective _) U' S'
  let e₂ : ((map ι (comap q S')).subquotient (map ι (comap q U'))).Equiv
      ((comap q S').subquotient (comap q U')) :=
    (subquotientEquivOfIntertwiningMap ι (U := comap q U') (S := comap q S')
      (U' := map ι (comap q U')) (S' := map ι (comap q S')) (fun x hx ↦ ⟨x, hx, rfl⟩)
      (fun x _ hx ↦ ⟨x, hx, rfl⟩) (fun x _ hx ↦ by
        obtain ⟨y, hy, hxy⟩ := mem_map.1 hx
        exact hι hxy ▸ hy) fun y hy ↦ by
        obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
        exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩).symm
  exact ⟨_, _, ⟨e₂.trans e₁⟩⟩

/-- Every irreducible subquotient `S / U` of `ρ` with `S ≤ F n`, for a chain of
subrepresentations `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n`, is equivalent to a subquotient of one of the steps
`F (i + 1) / F i`. -/
theorem exists_subquotient_equiv_of_chain {n : ℕ} {F : ℕ → Subrepresentation ρ}
    (h0 : F 0 = ⊥) (hF : ∀ i < n, F i ≤ F (i + 1)) {U S : Subrepresentation ρ} (hS : S ≤ F n)
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ i < n, ∃ U' S' : Subrepresentation ((F (i + 1)).subquotient (F i)),
      Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  induction n generalizing U S with
  | zero =>
    have := inf_lt_of_isIrreducible hirr
    rw [h0, le_bot_iff] at hS
    subst hS
    exact absurd this (by simp)
  | succ n ih =>
    by_cases h : F n ⊓ S ≤ U
    · -- the subquotient survives in `F (n + 1) / F n`
      let π : (F (n + 1)).toRepresentation.IntertwiningMap ((F (n + 1)).subquotient (F n)) :=
        ⟨Submodule.mkQ _, fun _ ↦ rfl⟩
      let ι : (F (n + 1)).toRepresentation.IntertwiningMap ρ := ⟨Submodule.subtype _, fun _ ↦ rfl⟩
      let e₁ : ((comap ι S).subquotient (comap ι U)).Equiv (S.subquotient U) :=
        subquotientEquivOfIntertwiningMap ι (fun _ hx ↦ hx) (fun _ _ hx ↦ hx) (fun _ _ hx ↦ hx)
          fun y hy ↦ ⟨⟨y, hS hy⟩, hy, (congrArg (· ∈ U) (sub_self y)).mpr U.toSubmodule.zero_mem⟩
      have hinj (x) (hxS : x ∈ comap ι S) (hx : π x ∈ map π (comap ι U ⊓ comap ι S)) :
          x ∈ comap ι U := by
        obtain ⟨u, hu, hux⟩ := mem_map.1 hx
        have hxu : ((x - u : (F (n + 1)).toSubmodule) : V) ∈ F n := by
          have : π (x - u) = 0 := by rw [map_sub, hux, sub_self]
          exact (Submodule.Quotient.mk_eq_zero
            ((F n).toSubmodule.comap (F (n + 1)).toSubmodule.subtype)).1 this
        have hxuS : ((x - u : (F (n + 1)).toSubmodule) : V) ∈ S :=
          S.toSubmodule.sub_mem hxS (mem_inf.1 hu).2
        have hu' : (u : V) ∈ U := (mem_inf.1 hu).1
        have := U.toSubmodule.add_mem (h (mem_inf.2 ⟨hxu, hxuS⟩)) hu'
        rwa [Submodule.coe_sub, sub_add_cancel] at this
      let e₂ : ((comap ι S).subquotient (comap ι U)).Equiv
          ((map π (comap ι S)).subquotient (map π (comap ι U ⊓ comap ι S))) :=
        subquotientEquivOfIntertwiningMap π (fun x hx ↦ mem_map.2 ⟨x, hx, rfl⟩)
          (fun x hxS hxU ↦ mem_map.2 ⟨x, mem_inf.2 ⟨hxU, hxS⟩, rfl⟩) hinj fun y hy ↦ by
            obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
            exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩
      exact ⟨n, Nat.lt_succ_self n, _, _, ⟨e₂.symm.trans e₁⟩⟩
    · -- the subquotient comes from `F n`
      let e : ((F n ⊓ S).subquotient U).Equiv (S.subquotient U) :=
        subquotientEquivOfIntertwiningMap (.id ρ) (fun _ hx ↦ (mem_inf.1 hx).2) (fun _ _ hx ↦ hx)
          (fun _ _ hx ↦ hx) fun y hy ↦ exists_mem_inf_sub_mem_of_isIrreducible hirr h hy
      obtain ⟨i, hi, U', S', ⟨e'⟩⟩ := ih (fun i hi ↦ hF i (by omega)) inf_le_left
        (e.isIrreducible_iff.2 hirr)
      exact ⟨i, by omega, U', S', ⟨e'.trans e⟩⟩

/-- Every irreducible subquotient `S / U` of `ρ` with `S ≤ P 0`, for a decreasing chain of
subrepresentations `P 0 ≥ P 1 ≥ ⋯ ≥ P n = 0`, is equivalent to a subquotient of one of the steps
`P j / P (j + 1)`. -/
theorem exists_subquotient_equiv_of_antitone_chain {n : ℕ} {P : ℕ → Subrepresentation ρ}
    (hn : P n = ⊥) (hP : ∀ j < n, P (j + 1) ≤ P j) {U S : Subrepresentation ρ} (hS : S ≤ P 0)
    (hirr : (S.subquotient U).IsIrreducible) :
    ∃ j < n, ∃ U' S' : Subrepresentation ((P j).subquotient (P (j + 1))),
      Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
  obtain ⟨i, hi, U', S', ⟨e⟩⟩ := exists_subquotient_equiv_of_chain (F := fun i ↦ P (n - i))
    (n := n) (by rw [Nat.sub_zero, hn]) (fun i hi ↦ by
      have h : n - i = n - (i + 1) + 1 := by omega
      rw [h]
      exact hP _ (by omega)) (by rwa [Nat.sub_self]) hirr
  have key (a b : ℕ) (ha : a = n - (i + 1)) (hb : b = n - i) :
      ∃ U' S' : Subrepresentation ((P a).subquotient (P b)),
        Nonempty ((S'.subquotient U').Equiv (S.subquotient U)) := by
    subst ha hb
    exact ⟨U', S', ⟨e⟩⟩
  exact ⟨n - (i + 1), by omega, key _ _ rfl (by omega)⟩

/-- The dimensions of the factors `F (i + 1) / F i` of a chain `0 = F 0 ≤ F 1 ≤ ⋯ ≤ F n` of
subrepresentations add up to the dimension of `F n`. -/
theorem sum_finrank_subquotient [FiniteDimensional k V] {n : ℕ} {F : ℕ → Subrepresentation ρ}
    (h0 : F 0 = ⊥) (hF : ∀ i < n, F i ≤ F (i + 1)) :
    ∑ i ∈ Finset.range n, Module.finrank k ((F (i + 1)).toSubmodule ⧸
      (F i).toSubmodule.comap (F (i + 1)).toSubmodule.subtype) =
      Module.finrank k (F n).toSubmodule := by
  induction n with
  | zero => rw [h0, toSubmodule_bot, finrank_bot, Finset.sum_range_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih fun i hi ↦ hF i (by omega)]
    have h := Submodule.finrank_quotient_add_finrank
      ((F n).toSubmodule.comap (F (n + 1)).toSubmodule.subtype)
    rw [(Submodule.comapSubtypeEquivOfLe (hF n (by omega))).finrank_eq] at h
    omega

/-- The subrepresentation `⊤` is equivalent to `ρ`. -/
def topEquiv : (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ :=
  .mk Submodule.topEquiv fun _ ↦ rfl

/-- `ρ` is the internal direct sum of the one-member family `⊤`. -/
theorem isInternal_const_top {ι : Type*} [Unique ι] :
    DirectSum.IsInternal fun _ : ι ↦ (⊤ : Subrepresentation ρ).toSubmodule :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_subsingleton _)
    (by simp)

/-- Let `ρ` be the internal direct sum of a finite family of irreducible subrepresentations `Vs`.
Then an irreducible subrepresentation `S` lies in the sum of those `Vs a` which are equivalent to
`S`: by Schur's lemma, the projection `S → Vs a` vanishes unless `S ≅ Vs a`. -/
theorem le_iSup_of_isInternal {ι : Type*} [Finite ι] [DecidableEq ι]
    {Vs : ι → Subrepresentation ρ} (hint : DirectSum.IsInternal fun a ↦ (Vs a).toSubmodule)
    (hVs : ∀ a, (Vs a).toRepresentation.IsIrreducible) {S : Subrepresentation ρ}
    (hS : S.toRepresentation.IsIrreducible) :
    S ≤ ⨆ (a) (_ : Nonempty (S.toRepresentation.Equiv (Vs a).toRepresentation)), Vs a := by
  have := Fintype.ofFinite ι
  let M : ι → Submodule k V := fun a ↦ (Vs a).toSubmodule
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap M) hint
  have hsum (x : DirectSum ι fun a ↦ M a) : e x = ∑ b, (x b : V) := by
    change DirectSum.coeLinearMap M x = _
    conv_lhs => rw [← DirectSum.sum_univ_of x]
    simp only [map_sum, DirectSum.coeLinearMap_of]
  -- the projection onto `Vs a` is intertwining
  have hproj (g : G) (v : V) (a : ι) : ((e.symm (ρ g v)) a : V) = ρ g (e.symm v a) := by
    set x := e.symm v
    let y : DirectSum ι fun a ↦ M a := DFinsupp.equivFunOnFintype.symm fun b ↦
      ⟨ρ g (x b), (Vs b).apply_mem_toSubmodule g (x b).2⟩
    have hy : e y = ρ g v := by
      rw [hsum, ← e.apply_symm_apply v, hsum, map_sum]
      rfl
    rw [← hy, e.symm_apply_apply]
    rfl
  intro v hv
  rw [← e.apply_symm_apply v, hsum]
  refine Submodule.sum_mem _ fun a _ ↦ ?_
  by_cases ha : Nonempty (S.toRepresentation.Equiv (Vs a).toRepresentation)
  · exact (le_iSup₂ (f := fun a (_ : Nonempty (S.toRepresentation.Equiv
      (Vs a).toRepresentation)) ↦ Vs a) a ha : _) (e.symm v a).2
  · let f : S.toRepresentation.IntertwiningMap (Vs a).toRepresentation :=
      ⟨DirectSum.component k ι (fun a ↦ M a) a ∘ₗ e.symm.toLinearMap ∘ₗ S.toSubmodule.subtype,
        fun g ↦ by
          ext w
          exact hproj g w a⟩
    have := hS
    have := hVs a
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
    · exact absurd ⟨Representation.IntertwiningMap.ofBijective f hf⟩ ha
    · have : (e.symm v a : V) = 0 := congrArg Subtype.val (congrArg (· ⟨v, hv⟩) hf :)
      rw [this]
      exact zero_mem _

/-- A finite family `Vs` of irreducible subrepresentations which is independent and spans `ρ`
gives a composition series `F i = ⨆_{j < i} Vs j` whose factors are the `Vs j`. -/
theorem exists_compositionSeries_of_iSupIndep {t : ℕ} {Vs : Fin t → Subrepresentation ρ}
    (hind : iSupIndep Vs) (htop : ⨆ i, Vs i = ⊤)
    (hirr : ∀ i, (Vs i).toRepresentation.IsIrreducible) :
    ∃ F : ℕ → Subrepresentation ρ, F 0 = ⊥ ∧ F t = ⊤ ∧ (∀ i < t, F i ⋖ F (i + 1)) ∧
      ∀ i : Fin t, Nonempty (((F (i + 1)).subquotient (F i)).Equiv (Vs i).toRepresentation) := by
  let F : ℕ → Subrepresentation ρ := fun i ↦ ⨆ (j : Fin t) (_ : (j : ℕ) < i), Vs j
  have hsucc (i : Fin t) : F (i + 1) = F i ⊔ Vs i := by
    refine le_antisymm (iSup₂_le fun j hj ↦ ?_) (sup_le (iSup₂_le fun j hj ↦ ?_) ?_)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · exact le_sup_of_le_left (le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < i) ↦ Vs j) j hj)
      · exact le_sup_of_le_right (le_of_eq (congrArg Vs (Fin.ext hj)))
    · exact le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < i + 1) ↦ Vs j) j (by omega)
    · exact le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < i + 1) ↦ Vs j) i (by omega)
  have hdisj (i : Fin t) : F i ⊓ Vs i = ⊥ :=
    (hind.disjoint_biSup (y := {j | (j : ℕ) < i}) (by simp)).symm.eq_bot
  have hequiv (i : Fin t) :
      Nonempty (((F (i + 1)).subquotient (F i)).Equiv (Vs i).toRepresentation) := by
    have h₁ : Nonempty (((Vs i).subquotient (F i ⊓ Vs i)).Equiv (Vs i).toRepresentation) := by
      rw [hdisj i]
      exact ⟨subquotientBotEquiv _⟩
    rw [hsucc i]
    exact ⟨(subquotientSupEquiv (F i) (Vs i)).symm.trans h₁.some⟩
  refine ⟨F, by simp [F], ?_, fun i hi ↦ ?_, hequiv⟩
  · simp only [F]
    rw [← htop]
    exact le_antisymm (iSup₂_le fun j _ ↦ le_iSup Vs j)
      (iSup_le fun j ↦ le_iSup₂ (f := fun (j : Fin t) (_ : (j : ℕ) < t) ↦ Vs j) j j.2)
  · have hle : F i ≤ F (i + 1) := by
      rw [show i + 1 = ((⟨i, hi⟩ : Fin t) : ℕ) + 1 from rfl, hsucc ⟨i, hi⟩]
      exact le_sup_left
    exact (isIrreducible_subquotient_iff hle).1
      ((hequiv ⟨i, hi⟩).some.isIrreducible_iff.2 (hirr _))

section Quotient

/-- The quotient representation `ρ / A` on `V ⧸ A` of a representation by a subrepresentation. -/
noncomputable def quotient (A : Subrepresentation ρ) :
    Representation k G (V ⧸ A.toSubmodule) where
  toFun g := A.toSubmodule.mapQ A.toSubmodule (ρ g) fun _ hx ↦ A.apply_mem_toSubmodule g hx
  map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ by simp)
  map_mul' _ _ := Submodule.linearMap_qext _ (LinearMap.ext fun _ ↦ by simp)

theorem quotient_apply_mk (A : Subrepresentation ρ) (g : G) (v : V) :
    A.quotient g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) :=
  rfl

/-- The projection `ρ → ρ / A`, as an intertwining map. -/
def mkQ (A : Subrepresentation ρ) : ρ.IntertwiningMap A.quotient :=
  ⟨A.toSubmodule.mkQ, fun _ ↦ rfl⟩

theorem mkQ_surjective (A : Subrepresentation ρ) : Function.Surjective A.mkQ :=
  Submodule.mkQ_surjective _

/-- The inclusion `A → ρ` of a subrepresentation, as an intertwining map. -/
def subtype (A : Subrepresentation ρ) : A.toRepresentation.IntertwiningMap ρ :=
  ⟨A.toSubmodule.subtype, fun _ ↦ rfl⟩

theorem subtype_injective (A : Subrepresentation ρ) : Function.Injective A.subtype :=
  Submodule.injective_subtype _

/-- The image of `A` under its inclusion is `A`. -/
theorem map_subtype_top (A : Subrepresentation ρ) : map A.subtype ⊤ = A :=
  toSubmodule_injective (Submodule.map_subtype_top _)

/-- The preimage of `0` under the projection `ρ → ρ / A` is `A`. -/
theorem comap_mkQ_bot (A : Subrepresentation ρ) : comap A.mkQ ⊥ = A :=
  toSubmodule_injective (Submodule.ker_mkQ _)

theorem map_bot {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k G V'}
    (f : ρ.IntertwiningMap σ) : map f ⊥ = ⊥ :=
  toSubmodule_injective (Submodule.map_bot _)

theorem comap_top {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k G V'}
    (f : ρ.IntertwiningMap σ) : comap f ⊤ = ⊤ :=
  toSubmodule_injective (Submodule.comap_top _)

theorem map_mono {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k G V'}
    (f : ρ.IntertwiningMap σ) {S T : Subrepresentation ρ} (h : S ≤ T) : map f S ≤ map f T :=
  fun _ ⟨x, hx, hxy⟩ ↦ ⟨x, h hx, hxy⟩

theorem comap_mono {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k G V'}
    (f : ρ.IntertwiningMap σ) {S T : Subrepresentation σ} (h : S ≤ T) : comap f S ≤ comap f T :=
  fun _ hx ↦ h hx

/-- An injective intertwining map `f` identifies the subquotient `f(S) / f(U)` with `S / U`. -/
noncomputable def subquotientMapEquiv {V' : Type*} [AddCommGroup V'] [Module k V']
    {σ : Representation k G V'} (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (U S : Subrepresentation ρ) : ((map f S).subquotient (map f U)).Equiv (S.subquotient U) :=
  (subquotientEquivOfIntertwiningMap f (U := U) (S := S) (U' := map f U) (S' := map f S)
    (fun x hx ↦ ⟨x, hx, rfl⟩) (fun x _ hx ↦ ⟨x, hx, rfl⟩)
    (fun x _ hx ↦ by
      obtain ⟨y, hy, hxy⟩ := mem_map.1 hx
      exact hf hxy ▸ hy) fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
      exact ⟨x, hx, by rw [sub_self]; exact Submodule.zero_mem _⟩).symm

/-- Composition series of a subrepresentation `A` and of the quotient `ρ / A`, of lengths `m`
and `n`, can be concatenated to a composition series of `ρ` of length `m + n` whose first `m`
factors are those of `A` and whose last `n` factors are those of `ρ / A`. -/
theorem exists_compositionSeries_append (A : Subrepresentation ρ) {m n : ℕ}
    {F₁ : ℕ → Subrepresentation A.toRepresentation} (h₁0 : F₁ 0 = ⊥) (h₁m : F₁ m = ⊤)
    (h₁ : ∀ i < m, F₁ i ⋖ F₁ (i + 1))
    {F₂ : ℕ → Subrepresentation A.quotient} (h₂0 : F₂ 0 = ⊥) (h₂n : F₂ n = ⊤)
    (h₂ : ∀ i < n, F₂ i ⋖ F₂ (i + 1)) :
    ∃ F : ℕ → Subrepresentation ρ, F 0 = ⊥ ∧ F (m + n) = ⊤ ∧ (∀ i < m + n, F i ⋖ F (i + 1)) ∧
      (∀ i < m,
        Nonempty (((F (i + 1)).subquotient (F i)).Equiv ((F₁ (i + 1)).subquotient (F₁ i)))) ∧
      ∀ i < n, Nonempty (((F (m + i + 1)).subquotient (F (m + i))).Equiv
        ((F₂ (i + 1)).subquotient (F₂ i))) := by
  let F : ℕ → Subrepresentation ρ := fun i ↦
    if i ≤ m then map A.subtype (F₁ i) else comap A.mkQ (F₂ (i - m))
  have hF₁ {i : ℕ} (hi : i ≤ m) : F i = map A.subtype (F₁ i) := if_pos hi
  have hF₂ (i : ℕ) : F (m + i) = comap A.mkQ (F₂ i) := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [add_zero, hF₁ le_rfl, h₁m, h₂0, map_subtype_top, comap_mkQ_bot]
    · exact (if_neg (by omega)).trans (by rw [Nat.add_sub_cancel_left])
  have he₁ (i : ℕ) (hi : i < m) :
      Nonempty (((F (i + 1)).subquotient (F i)).Equiv ((F₁ (i + 1)).subquotient (F₁ i))) := by
    rw [hF₁ hi.le, hF₁ hi]
    exact ⟨subquotientMapEquiv _ A.subtype_injective _ _⟩
  have he₂ (i : ℕ) (_ : i < n) : Nonempty (((F (m + i + 1)).subquotient (F (m + i))).Equiv
      ((F₂ (i + 1)).subquotient (F₂ i))) := by
    rw [add_assoc, hF₂, hF₂]
    exact ⟨subquotientComapEquiv _ A.mkQ_surjective _ _⟩
  refine ⟨F, by rw [hF₁ (Nat.zero_le m), h₁0, map_bot], by rw [hF₂, h₂n, comap_top],
    fun i hi ↦ ?_, he₁, he₂⟩
  rcases lt_or_ge i m with him | him
  · have hle : F i ≤ F (i + 1) := by
      rw [hF₁ him.le, hF₁ him]
      exact map_mono _ (h₁ i him).le
    obtain ⟨e⟩ := he₁ i him
    exact (isIrreducible_subquotient_iff hle).1 (e.isIrreducible_iff.2
      ((isIrreducible_subquotient_iff (h₁ i him).le).2 (h₁ i him)))
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le him
    have hi' : i < n := by omega
    have hle : F (m + i) ≤ F (m + i + 1) := by
      rw [add_assoc, hF₂, hF₂]
      exact comap_mono _ (h₂ i hi').le
    obtain ⟨e⟩ := he₂ i hi'
    exact (isIrreducible_subquotient_iff hle).1 (e.isIrreducible_iff.2
      ((isIrreducible_subquotient_iff (h₂ i hi').le).2 (h₂ i hi')))

end Quotient

end Subrepresentation
