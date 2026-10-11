module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Change of ideal for adic completion
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion) -/

@[expose] public section

open scoped Pointwise


/-- `J ^ (d * k) M ⊆ I ^ k M` when `J ^ d ⊆ I`: the inclusion making the reduction
`M/J^{dk}M → M/I^kM` of the comparison map well defined.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: `J ^ (d * k) = (J ^ d) ^ k ≤ I ^ k`, and `• ⊤` is monotone in the ideal. -/
theorem powerReductionJI {A : Type*} [CommRing A] (I J : Ideal A) (d k : ℕ)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hJI : J ^ d ≤ I) :
    J ^ (d * k) • (⊤ : Submodule A M) ≤ I ^ k • (⊤ : Submodule A M) := by sorry

/-- `I ^ (c * n) M ⊆ J ^ n M` when `I ^ c ⊆ J`: the inclusion making the reduction
`M/I^{cn}M → M/J^nM` of the inverse comparison map well defined.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: `I ^ (c * n) = (I ^ c) ^ n ≤ J ^ n`, and `• ⊤` is monotone in the ideal. -/
theorem powerReductionIJ {A : Type*} [CommRing A] (I J : Ideal A) (c n : ℕ)
    (M : Type*) [AddCommGroup M] [Module A M]
    (hIJ : I ^ c ≤ J) :
    I ^ (c * n) • (⊤ : Submodule A M) ≤ J ^ n • (⊤ : Submodule A M) := by sorry

/-- Completions for two cofinal ideals are canonically isomorphic.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: the systems of maps `M/J^{dk}M → M/I^kM` and `M/I^{cn}M → M/J^nM` are
compatible with the transition maps and `A`-linear, so they give maps
`θ : M^∧_J → M^∧_I` and `θ' : M^∧_I → M^∧_J`; both composites are computed
componentwise to be the identity (`x_{cdk}` reduces to `x_k`), so `θ` is a linear
equivalence. Both `θ ∘ ι_J` and `ι_I` send `x` to `(x mod I^kM)_k`, so they agree;
hence `ι_I` is bijective iff `ι_J = θ⁻¹ ∘ ι_I` is. -/
theorem changeIdealCompletion
    {A : Type*} [CommRing A] (I J : Ideal A) (c d : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I)
    (M : Type*) [AddCommGroup M] [Module A M] :
    ∃ (θ : AdicCompletion J M ≃ₗ[A] AdicCompletion I M),
      (∀ (x : AdicCompletion J M) (k : ℕ),
        (θ x).val k =
          Submodule.factor (show J ^ (d * k) • (⊤ : Submodule A M) ≤
            I ^ k • (⊤ : Submodule A M) by exact powerReductionJI I J d k M hJI) (x.val (d * k))) ∧
      (∀ (x : AdicCompletion I M) (n : ℕ),
        (θ.symm x).val n =
          Submodule.factor (show I ^ (c * n) • (⊤ : Submodule A M) ≤
            J ^ n • (⊤ : Submodule A M) by exact powerReductionIJ I J c n M hIJ) (x.val (c * n))) ∧
      (∀ (x : M), θ (AdicCompletion.of J M x) = AdicCompletion.of I M x) ∧
      (Function.Bijective (AdicCompletion.of I M) ↔
        Function.Bijective (AdicCompletion.of J M))
    := by sorry


/-- For `M = A` the comparison `θ : A^∧_J → A^∧_I`, `(x_n)_n ↦ (x_{dk} mod I^k)_k`,
is a ring equivalence.
Source: literature/stacks-project/algebra.tex, Algebra Lemma Tag 0319
(blueprint: lem-weil-pbc-change-ideal-completion).
Proof: `θ` is the linear equivalence of `changeIdealCompletion` for `M = A`; each
reduction `A/J^{dk} → A/I^k` is a ring map and multiplication on both completions
is componentwise, so `θ` preserves `1` and products. -/
theorem changeIdealCompletionRing
    {A : Type*} [CommRing A] (I J : Ideal A) (c d : ℕ)
    (hc : 1 ≤ c) (hd : 1 ≤ d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    ∃ e : AdicCompletion J A ≃+* AdicCompletion I A,
      (∀ (x : AdicCompletion J A) (k : ℕ),
        (e x).val k =
          Submodule.factor (show J ^ (d * k) • (⊤ : Submodule A A) ≤
            I ^ k • (⊤ : Submodule A A) by exact powerReductionJI I J d k A hJI)
            (x.val (d * k))) := by sorry
