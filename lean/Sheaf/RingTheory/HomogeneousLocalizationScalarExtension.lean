/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Scalar extension of degree-zero homogeneous localization

Source: Stacks Project, constructions.tex, Tag 01N2 (lemma-base-change-map-proj),
standard-open calculation, with the chart fractions of Tag 01M4 (lemma-standard-open).
(blueprint: lem-nagata-homogeneous-localization-scalar-extension)
-/

@[expose] public section

universe u v w

open TensorProduct

namespace HomogeneousLocalization

/-- Scalar extension commutes with degree-zero homogeneous localization, with its prescribed
formula on pure tensors of fractions. Source: Stacks Project, constructions.tex, Tag 01N2,
proof of lemma-base-change-map-proj; fraction convention of Tag 01M4.
(blueprint: lem-nagata-homogeneous-localization-scalar-extension)

Proof: First compare fractions at a common later denominator: a power-annihilated
localization relation gives equality after multiplying the numerators by suitable powers
of f, and conversely such equality gives a localization relation. No cancellation is used.
Second, each graded piece inclusion has an R-linear projection splitting it; tensoring
retains this splitting without flatness. Thus every numerator in the base-changed graded
piece is a finite sum of homogeneous pure tensors. The balanced maps a ↦ a/f^m induce
maps q_m from these pieces into S ⊗[R] Away 𝒜 f. They satisfy
q_(m+1)(f_S c) = q_m(c), hence define an inverse on fractions by the common-denominator
criterion. Third, the displayed formula is additive in each variable and R-balanced,
again by common denominators, so descends to the tensor product. The two composites
are identities on pure tensors and on finite sums of homogeneous numerators.
Finally, multiplying fractions proves multiplicativity on pure tensors and hence on
finite sums; 1 ⊗ (1/1) maps to 1/1 and s ⊗ (1/1) maps to the scalar s. This gives the
asserted S-algebra equivalence. These steps use
[def-nagata-homogeneous-localization-degree-zero] throughout and allow zero divisors. -/
theorem exists_away_scalarExtension_equiv
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    ∃ e : (S ⊗[R] Away 𝒜 f) ≃ₐ[S]
        Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f),
      ∀ (s : S) (m : ℕ) (a : A) (ha : a ∈ 𝒜 (m • d)),
        e (s ⊗ₜ[R] Away.mk 𝒜 hf m a ha) =
          Away.mk (fun n ↦ (𝒜 n).baseChange S)
            (Submodule.tmul_mem_baseChange_of_mem 1 hf) m (s ⊗ₜ[R] a)
            (Submodule.tmul_mem_baseChange_of_mem s ha) := by
  sorry

end HomogeneousLocalization
