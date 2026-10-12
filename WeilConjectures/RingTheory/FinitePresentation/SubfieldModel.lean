/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Finset.Order

/-!
# Finitely presented algebras over a directed union of subfields

Let `k` be a field which is the directed union of subfields `K i`. Every finitely presented
`k`-algebra `E` descends to one of the `K i`: there is a `K i`-algebra `B` with
`k ⊗[K i] B ≃ₐ[k] E` (Stacks, proof of Lemma 07QG).

## Main results

- `Algebra.exists_subfield_model`
-/

@[expose] public section

universe u w

open TensorProduct

namespace Algebra

/-- Let `k` be a field, `(K i)` a nonempty directed family of subfields of `k` whose union is
`k`, and `E` a finitely presented `k`-algebra. Then for some `i` there is a commutative
`K i`-algebra `B` (in `Type (max u w)`) with `k ⊗[K i] B ≃ₐ[k] E`.
(blueprint: `lem-weil-pbc-finite-presentation-subfield-model`) -/
theorem exists_subfield_model {k : Type u} {E : Type w} [Field k] [CommRing E] [Algebra k E]
    [FinitePresentation k E] {ι : Type*} [Nonempty ι] (K : ι → Subfield k)
    (hdir : Directed (· ≤ ·) K) (hunion : ⋃ i, (K i : Set k) = Set.univ) :
    ∃ i, ∃ (B : Type (max u w)) (_ : CommRing B) (_ : Algebra (K i) B),
      Nonempty (k ⊗[K i] B ≃ₐ[k] E) := by
  classical
  obtain ⟨n, I, eI, hI⟩ := FinitePresentation.iff.1 ‹_›
  obtain ⟨s, hs⟩ := hI
  have hmem : ∀ c : k, ∃ i, c ∈ K i := fun c ↦ by
    simpa using (Set.ext_iff.1 hunion c).2 trivial
  choose j hj using hmem
  obtain ⟨i, hi⟩ := hdir.finset_le ((s.biUnion MvPolynomial.coeffs).image j)
  have hcoeff : ∀ p ∈ s, ∀ c ∈ p.coeffs, c ∈ K i := fun p hp c hc ↦
    hi (j c) (Finset.mem_image.2 ⟨c, Finset.mem_biUnion.2 ⟨p, hp, hc⟩, rfl⟩) (hj c)
  let φ : MvPolynomial (Fin n) (K i) →+* MvPolynomial (Fin n) k :=
    MvPolynomial.map (algebraMap (K i) k)
  let J₀ : Ideal (MvPolynomial (Fin n) (K i)) := I.comap φ
  have hJ : I = J₀.map φ := by
    refine le_antisymm ?_ (Ideal.map_comap_le)
    rw [← hs, Ideal.span_le]
    intro p hp
    have : p ∈ Set.range φ := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      exact ⟨⟨c, hcoeff p hp c hc⟩, rfl⟩
    obtain ⟨q, rfl⟩ := this
    exact Ideal.mem_map_of_mem _ (show φ q ∈ I from hs ▸ Ideal.subset_span hp)
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) (K i) k
  have he : (e : k ⊗[K i] MvPolynomial (Fin n) (K i) →+* MvPolynomial (Fin n) k).comp
      (TensorProduct.includeRight.toRingHom) = φ := by
    ext x
    · simp [φ, e]
    · simp [φ, e]
  have hJ' : I = (J₀.map (TensorProduct.includeRight (R := K i) (A := k)
      (B := MvPolynomial (Fin n) (K i)))).map
        (e : k ⊗[K i] MvPolynomial (Fin n) (K i) →+* MvPolynomial (Fin n) k) := by
    rw [hJ, ← he, ← Ideal.map_map]
    rfl
  refine ⟨i, ULift.{max u w} (MvPolynomial (Fin n) (K i) ⧸ J₀), inferInstance, inferInstance,
    ⟨?_⟩⟩
  exact (TensorProduct.congr AlgEquiv.refl ULift.algEquiv).trans <|
    (TensorProduct.tensorQuotientEquiv k _ k J₀).trans <|
    (Ideal.quotientEquivAlg _ _ e hJ').trans eI

end Algebra
