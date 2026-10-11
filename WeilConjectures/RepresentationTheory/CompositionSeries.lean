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

end Subrepresentation
