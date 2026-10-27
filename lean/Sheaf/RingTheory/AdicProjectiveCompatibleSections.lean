module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Compatible sections of projective adic quotients

Source: Stacks Project, Tag 05D3, proof of `lemma-split-completed-sequence`,
the induction constructing quotient splittings
(blueprint: lem-trf-adic-projective-compatible-sections).

The natural-number index `n` denotes the positive quotient level `n + 1`.
The quotient maps are Mathlib's `LinearMap.reduceModIdeal` and
`Submodule.factorPowSucc`; compatibility is stated after restriction of scalars to `R`.
-/

@[expose] public section

universe u v w

namespace Module

/-- A prescribed section of a projective adic quotient extends one level, and compatible
sections exist at all positive levels.

Source: Stacks Project, Tag 05D3, proof of `lemma-split-completed-sequence`
(blueprint: lem-trf-adic-projective-compatible-sections).

Proof:
1. The submodule `I^k L` consists of finite sums of terms `a • x` with `a ∈ I^k`.
   Thus `v` induces the surjective quotient maps `v_k`; inclusion of consecutive
   ideal powers gives reductions, and the quotient maps commute with reduction.
2. Given a section `s_n`, let `P` be the inverse image in `E` of its image in `E_n`.
   It contains `I^n E`. For `z ∈ P`, the section identity gives
   `p_n(z) = s_n(p_n(v(z)))`.
3. The restriction `P → M` is surjective. Lift `s_n(p_n(m))` to `z ∈ E`.
   The error `m - v(z)` belongs to `I^n M`. Express it as a finite sum `∑ a_j m_j`,
   lift each `m_j` along `v`, and add `∑ a_j e_j ∈ I^n E ⊆ P` to `z`.
   Its image is `m`. This includes the empty sum and needs no finiteness or flatness.
4. The maps `π : P/I^(n+1) P → M_(n+1)` and
   `j : P/I^(n+1) P → E_(n+1)`, given by `v` and inclusion, are well defined
   and linear over `R/I^(n+1)`. The map `π` is surjective and `v_(n+1) ∘ j = π`.
   Injectivity of `j` is neither claimed nor used.
5. Projectivity of `M_(n+1)` (def-weil-pbc-projective-module) lifts its identity
   along `π` to a section `t`. Then `s_(n+1) = j ∘ t` is a quotient-linear section.
6. On representatives in `P`, Step 2 gives `q_n ∘ j = s_n ∘ q_n ∘ π`.
   Compose with `t` to obtain compatibility as an equality of `R`-linear maps.
7. Projectivity of `M_1` (def-weil-pbc-projective-module) supplies a first section
   of the surjection `v_1`. Choose compatible successors using Steps 2--6 and
   recurse to obtain the family at every positive level. -/
theorem adic_projective_compatible_sections
    {R : Type u} [CommRing R] (I : Ideal R)
    {E : Type v} [AddCommGroup E] [Module R E]
    {M : Type w} [AddCommGroup M] [Module R M]
    (v : E →ₗ[R] M) (hv : Function.Surjective v)
    (hprojective : ∀ n : ℕ,
      Module.Projective (R ⧸ I ^ (n + 1)) (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))) :
    (∀ (n : ℕ)
      (s : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
        E ⧸ (I ^ (n + 1) • ⊤ : Submodule R E)),
      (v.reduceModIdeal (I ^ (n + 1))).comp s = LinearMap.id →
      ∃ t : M ⧸ (I ^ (n + 1 + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1 + 1)]
          E ⧸ (I ^ (n + 1 + 1) • ⊤ : Submodule R E),
        (v.reduceModIdeal (I ^ (n + 1 + 1))).comp t = LinearMap.id ∧
        (Submodule.factorPowSucc I E (n + 1)).comp (t.restrictScalars R) =
          (s.restrictScalars R).comp (Submodule.factorPowSucc I M (n + 1))) ∧
    (∃ s : (n : ℕ) →
        M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R ⧸ I ^ (n + 1)]
          E ⧸ (I ^ (n + 1) • ⊤ : Submodule R E),
      ∀ n : ℕ,
        (v.reduceModIdeal (I ^ (n + 1))).comp (s n) = LinearMap.id ∧
        (Submodule.factorPowSucc I E (n + 1)).comp ((s (n + 1)).restrictScalars R) =
          ((s n).restrictScalars R).comp (Submodule.factorPowSucc I M (n + 1))) := by
  sorry

end Module
