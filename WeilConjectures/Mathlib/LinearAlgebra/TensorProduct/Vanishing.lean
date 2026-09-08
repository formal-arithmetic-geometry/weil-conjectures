/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Vanishing

/-!
# Equational criterion for vanishing, without a spanning hypothesis

Mathlib's `TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero` shows that a vanishing expression
$\sum_i m_i \otimes n_i = 0$ in $M \otimes_R N$ vanishes trivially provided the $m_i$ generate $M$.
Here we remove the generation hypothesis at the cost of enlarging the family: any vanishing
expression becomes trivially vanishing after adjoining finitely many auxiliary elements of $M$,
paired with the zero element of $N$.

## Main results

- `TensorProduct.exists_vanishesTrivially_extension`
-/

@[expose] public section

open Function LinearMap

namespace TensorProduct

variable (R : Type*) [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {ι : Type*} [Fintype ι] {m : ι → M} {n : ι → N}

/-- **Equational criterion for vanishing**, extension-of-family form.

If $\sum_i m_i \otimes n_i = 0$ in $M \otimes_R N$, then there are finitely many auxiliary
elements $m'_1, \dots, m'_l$ of $M$ such that the enlarged expression
$\sum_i m_i \otimes n_i + \sum_{i'} m'_{i'} \otimes 0$ vanishes trivially. Compare
`TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero`, which needs the $m_i$ to generate $M$. -/
theorem exists_vanishesTrivially_extension (hmn : ∑ i, m i ⊗ₜ n i = (0 : M ⊗[R] N)) :
    ∃ (l : ℕ) (m' : Fin l → M), VanishesTrivially R (Sum.elim m m') (Sum.elim n 0) := by
  classical
  /- Define a surjective map `G` from the free module on `ι ⊕ M` to `M`, sending the basis vector
  at `Sum.inl i` to `m i` and the one at `Sum.inr x` to `x`. -/
  set v : ι ⊕ M → M := Sum.elim m id with hv
  set G : ((ι ⊕ M) →₀ R) →ₗ[R] M := Finsupp.linearCombination R v with hG
  have G_basis_eq (q : ι ⊕ M) : G (Finsupp.single q 1) = v q := by simp [hG]
  have G_surjective : Surjective G := fun x ↦ ⟨Finsupp.single (Sum.inr x) 1, by simp [hG, hv]⟩
  /- The element `∑ i, e_{inl i} ⊗ n i` lies in the kernel of `rTensor N G`. -/
  set en : ((ι ⊕ M) →₀ R) ⊗[R] N := ∑ i, Finsupp.single (Sum.inl i : ι ⊕ M) 1 ⊗ₜ n i with hen
  have en_mem_ker : en ∈ ker (rTensor N G) := by simp [hen, G_basis_eq, hv, hmn]
  -- Tensoring the exact sequence `ker G → (ι ⊕ M) →₀ R → M → 0` with `N` stays exact.
  have exact_rTensor : Exact (rTensor N (ker G).subtype) (rTensor N G) :=
    rTensor_exact (M := ↥(ker G)) N G.exact_subtype_ker_map G_surjective
  have en_mem_range : en ∈ range (rTensor N (ker G).subtype) :=
    exact_rTensor.linearMap_ker_eq ▸ en_mem_ker
  obtain ⟨kn, hkn⟩ := en_mem_range
  obtain ⟨ma, rfl : kn = ∑ kj ∈ ma, kj.1 ⊗ₜ[R] kj.2⟩ := exists_finset kn
  /- Reading off the coordinate at `q` of both sides of `hkn`. -/
  have key (q : ι ⊕ M) : ∑ j ∈ ma, ((j.1 : (ι ⊕ M) →₀ R) q) • j.2
      = ∑ i, ((Finsupp.single (Sum.inl i : ι ⊕ M) (1 : R)) q) • n i := by
    have h := congrArg
      ((TensorProduct.lid R N).toLinearMap ∘ₗ rTensor N (Finsupp.lapply q)) hkn
    simpa [hen] using h
  /- The auxiliary elements: those `x : M` such that `Sum.inr x` occurs in the support of one of
  the kernel components. -/
  set T : Finset (ι ⊕ M) := ma.biUnion (fun j ↦ (j.1 : (ι ⊕ M) →₀ R).support) with hT
  set A : Finset M := T.preimage Sum.inr Sum.inr_injective.injOn with hA
  set m' : Fin A.card → M := fun t ↦ (A.equivFin.symm t : M) with hm'
  have hm'_inj : Injective m' := fun a b h ↦ A.equivFin.symm.injective (Subtype.ext h)
  have hm'_surj {x : M} (hx : x ∈ A) : ∃ t, m' t = x :=
    ⟨A.equivFin ⟨x, hx⟩, by simp [hm']⟩
  set ρ : ι ⊕ Fin A.card → ι ⊕ M := Sum.elim Sum.inl (fun t ↦ Sum.inr (m' t)) with hρ
  have ρ_inj : Injective ρ := by
    rw [hρ, Sum.elim_injective]
    exact ⟨Sum.inl_injective, Sum.inr_injective.comp hm'_inj, fun a b ↦ Sum.inl_ne_inr⟩
  refine ⟨A.card, m', VanishesTrivially.of_fintype (κ := ma)
    (fun p j ↦ (j.1.1 : (ι ⊕ M) →₀ R) (ρ p)) (fun j ↦ j.1.2) ?_ ?_⟩
  · -- The relations expressing `n i` (resp. `0`) in terms of the `y j`.
    intro p
    rw [Finset.univ_eq_attach, Finset.sum_attach ma (fun j ↦ (j.1 : (ι ⊕ M) →₀ R) (ρ p) • j.2),
      key (ρ p)]
    obtain (i | t) := p
    · simp [hρ, Finsupp.single_apply]
    · simp [hρ]
  · -- The relations `∑ i, a i j • m i = 0`, which come from `G (k j) = 0`.
    rintro ⟨⟨⟨f, hf⟩, y⟩, hjmem⟩
    have hsupp : f.support ⊆ Finset.univ.image ρ := by
      intro q hq
      obtain (i | x) := q
      · exact Finset.mem_image.mpr ⟨Sum.inl i, Finset.mem_univ _, rfl⟩
      · have hxT : (Sum.inr x : ι ⊕ M) ∈ T :=
          Finset.mem_biUnion.mpr ⟨(⟨f, hf⟩, y), hjmem, hq⟩
        obtain ⟨t, rfl⟩ := hm'_surj (Finset.mem_preimage.mpr hxT)
        exact Finset.mem_image.mpr ⟨Sum.inr t, Finset.mem_univ _, rfl⟩
    have hG0 : ∑ q ∈ Finset.univ.image ρ, f q • v q = 0 := by
      rw [← Finset.sum_subset hsupp (fun q _ hq ↦ by
        simp [Finsupp.notMem_support_iff.mp hq])]
      simpa [hG, Finsupp.linearCombination_apply, Finsupp.sum] using mem_ker.mp hf
    rw [Finset.sum_image (fun a _ b _ h ↦ ρ_inj h)] at hG0
    refine Eq.trans (Finset.sum_congr rfl fun p _ ↦ ?_) hG0
    obtain (i | t) := p
    · simp [hρ, hv]
    · simp [hρ, hv]

end TensorProduct
