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
end Subrepresentation
