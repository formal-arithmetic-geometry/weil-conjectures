/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# A finitely generated common extension of finitely many fields

Source: Stacks Project, Fields, Tag 0H7K, lemma-common-extension-field, and Varieties,
Tag 04KT, the simultaneous generic-field step
(blueprint: lem-pur-finite-family-common-extension).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Algebra

/-- A finite family of finitely generated extensions of k embeds in a common finitely
generated extension of k.

Source: Stacks Project, Fields, Tag 0H7K, lemma-common-extension-field; the finite-generation
refinement used for Varieties, Tag 04KT
(blueprint: lem-pur-finite-family-common-extension).

Proof: induct on the length of the family. The empty family embeds in k. Given a common
finitely generated field E for the tail and the remaining field K, form A = E tensor_k K.
This is nonzero because both fields contain k. Choose a maximal ideal m and let Q = A/m.
Both E and K map to the nonzero field Q by unital, hence injective, k-algebra maps.
The tensor product is essentially of finite type over E by base change from K/k, hence
over k by composition. Its quotient Q is therefore essentially of finite type over k,
which for a field means finitely generated as a field. Compose the tail embeddings with
E to Q and use K to Q for the head. -/
theorem exists_fg_common_field (k : Type u) [Field k] :
    ∀ (n : ℕ) (K : Fin n → Type u) [∀ i, Field (K i)] [∀ i, Algebra k (K i)],
      (∀ i, (⊤ : IntermediateField k (K i)).FG) →
      ∃ (E : Type u) (_ : Field E) (_ : Algebra k E),
        (⊤ : IntermediateField k E).FG ∧ Nonempty (∀ i, K i →ₐ[k] E) := by
  intro n
  induction n with
  | zero =>
      intro K _ _ _
      refine ⟨k, inferInstance, inferInstance, ?_, ⟨fun i ↦ Fin.elim0 i⟩⟩
      exact IntermediateField.fg_top_iff.mpr inferInstance
  | succ n ih =>
      intro K _ _ hK
      obtain ⟨E, hE, aE, hfg, ⟨emb⟩⟩ := ih (fun i ↦ K i.succ) (fun i ↦ hK i.succ)
      let := hE
      let := aE
      have : Algebra.EssFiniteType k E := IntermediateField.fg_top_iff.mp hfg
      have : Algebra.EssFiniteType k (K 0) := IntermediateField.fg_top_iff.mp (hK 0)
      let A := E ⊗[k] K 0
      have : Algebra.EssFiniteType k A := Algebra.EssFiniteType.comp k E A
      have : Nontrivial A :=
        Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k E (K 0)
          (algebraMap k E).injective (algebraMap k (K 0)).injective
      obtain ⟨m, hm⟩ := Ideal.exists_maximal A
      let := hm
      let Q := A ⧸ m
      let := Ideal.Quotient.field m
      let e : E →ₐ[k] Q := (Ideal.Quotient.mkₐ k m).comp
        (Algebra.TensorProduct.includeLeft : E →ₐ[k] A)
      let e₀ : K 0 →ₐ[k] Q := (Ideal.Quotient.mkₐ k m).comp
        (Algebra.TensorProduct.includeRight : K 0 →ₐ[k] A)
      exact ⟨Q, inferInstance, inferInstance,
        IntermediateField.fg_top_iff.mpr inferInstance,
        ⟨Fin.cases e₀ (fun i ↦ e.comp (emb i))⟩⟩

end Algebra
