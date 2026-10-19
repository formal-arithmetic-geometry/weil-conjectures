/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Adic evaluation of completed sharp monoid algebras

Source: Stacks Project, Algebra, Tag 05GG, lemma-hathat-finitely-generated;
agent-supplied evaluation and congruence refinement for ILO VI 2.3
(blueprint: lem-per-formal-monoid-adic-evaluation).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace AddMonoidAlgebra

/-- Every admissible monoid map has a unique continuous evaluation on the completed
monoid algebra. Evaluation preserves ideal powers, and congruence on any finite
nonzero generating family implies congruence on the entire completion.

Source: Stacks Project, Algebra, Tag 05GG, lemma-hathat-finitely-generated;
agent-supplied evaluation and congruence refinement for ILO VI 2.3
(blueprint: lem-per-formal-monoid-adic-evaluation).

The equation `hb` names the defining ideal, without imposing an extra condition.
The formula on `single p c` combines the coefficient and monomial requirements:
`p = 0` gives the coefficient map and `c = 1` gives the monomial map.
The source topology is the inverse-limit topology of the discrete quotients.

Natural-language proof (the seven steps of the DAG node):
1. Put `S = R[P]` and let `ι : S → B` be the canonical map. Choose generators
   `u_1, …, u_t` of `𝔞` and a finite generating list `q_1, …, q_h` of `P`
   with zero entries removed. Every nonzero `p` is a nonempty sum of the `q_i`,
   so `z^p` is a multiple of some `z^{q_i}`; hence
   `𝔟 = (u_1, …, u_t, z^{q_1}, …, z^{q_h})` is finitely generated. For
   `P = {0}` take the empty list.
2. Apply lem-weil-pbc-adic-completion-mod-power (Stacks 05GG (2)) to `S` and
   the finitely generated ideal `𝔟`: for `n ≥ 1` the projection
   `π_n : B → S / 𝔟^n` has kernel `𝔟^n B` and `π_n ι(g) = g mod 𝔟^n`. For
   `f ∈ B` choose `g_n ∈ S` representing `π_n(f)`; then `f - ι(g_n) ∈ 𝔟^n B`.
   The coordinate-kernel neighbourhoods and the `(𝔟B)`-adic ones coincide,
   since `(𝔟B)^n = 𝔟^n B`.
3. Define `e_a : S → A` by `e_a(∑ c_p z^p) = ∑ α(c_p) a(p)`. It preserves
   addition and the unit since `a(0) = 1`; expanding two finite supports uses
   only `a(p + q) = a(p) a(q)`, so it is multiplicative without cancellation in
   `P`. The generators of `𝔟` go into `J`, so `e_a(𝔟^n) ⊆ J^n` for `n ≥ 0`.
4. Thus `ē_{a,n} : S / 𝔟^n → A / J^n` is a well-defined ring map, compatible
   with reduction for `m ≤ n`. So `f ↦ (ē_{a,n}(π_n f))_n` is a ring map to
   `lim A / J^n` (def-weil-pbc-adic-completion). Compose with the inverse of the
   canonical isomorphism `A ≅ lim A / J^n` (def-weil-pbc-adically-complete-ring)
   to get `E_a` with `E_a(f) mod J^n = ē_{a,n}(π_n f)`. Taking `f = ι(g)` and
   separatedness give `E_a ι = e_a`, hence the values on `R` and on each `z^p`.
5. An element of `𝔟^n B` is a finite sum `∑ ι(v_j) f_j` with `v_j ∈ 𝔟^n`, so
   `E_a` sends it to `∑ e_a(v_j) E_a(f_j) ∈ J^n`; `n = 0` is `E_a(B) ⊆ A`. The
   preimage of `J^n` contains the open ideal `𝔟^n B` of step 2, and translation
   gives continuity at every point.
6. Let `F : B → A` be a continuous ring map with the same coefficient and
   monomial values. Then `F ι = e_a` and, as in step 5, `F(𝔟^n B) ⊆ J^n`. With
   `g_n` from step 2, `F(f)` and `E_a(f)` both equal `e_a(g_n)` modulo `J^n`, so
   `F(f) - E_a(f) ∈ ⋂_n J^n = 0` (def-weil-pbc-adically-complete-ring).
7. Let `a, b` satisfy the congruences on `p_1, …, p_h`. Writing
   `p = p_{i_1} + ⋯ + p_{i_k}` (empty for `p = 0`), the telescoping identity
   `∏ x_j - ∏ y_j = ∑_j (x_j - y_j) ∏_{l<j} x_l ∏_{l>j} y_l` with
   `x_j = a(p_{i_j})`, `y_j = b(p_{i_j})` gives `a(p) - b(p) ∈ J^r`, hence
   `e_a(g) - e_b(g) ∈ J^r` for `g ∈ S`. For `f ∈ B` take `g_r` from step 2
   (lem-weil-pbc-adic-completion-mod-power); step 5 sends `f - ι(g_r)` into
   `J^r` under both evaluations, so
   `E_a f - E_b f = E_a(f - ι g_r) + (e_a g_r - e_b g_r) - E_b(f - ι g_r) ∈ J^r`.
-/
theorem exists_formalMonoid_adicEvaluation
    (R : Type u) [CommRing R] (aI : Ideal R) (haI : aI.FG)
    (P : Type v) [AddCommMonoid P]
    (hfg : ∃ s : Finset P, AddSubmonoid.closure (s : Set P) = ⊤)
    (hsharp : ∀ p : P, IsUnit (Multiplicative.ofAdd p) → p = 0)
    (bI : Ideal (AddMonoidAlgebra R P))
    (hbI : bI = Ideal.map (algebraMap R (AddMonoidAlgebra R P)) aI ⊔
      Ideal.span {z | ∃ p : P, p ≠ 0 ∧ z = single p (1 : R)})
    (A : Type w) [CommRing A] (J : Ideal A) [IsAdicComplete J A]
    (α : R →+* A) (hα : ∀ c : R, c ∈ aI → α c ∈ J)
    (a : Multiplicative P →* A)
    (ha : ∀ p : P, p ≠ 0 → a (Multiplicative.ofAdd p) ∈ J) :
    ∃ Ea : AdicCompletion bI (AddMonoidAlgebra R P) →+* A,
      @Continuous _ _
        (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ bI n) ⊥)
        J.adicTopology Ea ∧
      (∀ (p : P) (c : R),
        Ea (AdicCompletion.of bI (AddMonoidAlgebra R P) (single p c)) =
          α c * a (Multiplicative.ofAdd p)) ∧
      (∀ E : AdicCompletion bI (AddMonoidAlgebra R P) →+* A,
        @Continuous _ _
          (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ bI n) ⊥)
          J.adicTopology E →
        (∀ (p : P) (c : R),
          E (AdicCompletion.of bI (AddMonoidAlgebra R P) (single p c)) =
            α c * a (Multiplicative.ofAdd p)) → E = Ea) ∧
      (∀ (n : ℕ) (f : AdicCompletion bI (AddMonoidAlgebra R P)),
        f ∈ Ideal.map
          (algebraMap (AddMonoidAlgebra R P) (AdicCompletion bI (AddMonoidAlgebra R P)))
          (bI ^ n) → Ea f ∈ J ^ n) ∧
      ∀ (b : Multiplicative P →* A)
        (_hb : ∀ p : P, p ≠ 0 → b (Multiplicative.ofAdd p) ∈ J)
        (Eb : AdicCompletion bI (AddMonoidAlgebra R P) →+* A),
        @Continuous _ _
          (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ bI n) ⊥)
          J.adicTopology Eb →
        (∀ (p : P) (c : R),
          Eb (AdicCompletion.of bI (AddMonoidAlgebra R P) (single p c)) =
            α c * b (Multiplicative.ofAdd p)) →
        ∀ (h : ℕ) (p : Fin h → P),
          (∀ i : Fin h, p i ≠ 0) →
          AddSubmonoid.closure (Set.range p) = ⊤ →
          ∀ r : ℕ, 1 ≤ r →
            (∀ i : Fin h,
              a (Multiplicative.ofAdd (p i)) - b (Multiplicative.ofAdd (p i)) ∈ J ^ r) →
            ∀ f : AdicCompletion bI (AddMonoidAlgebra R P), Ea f - Eb f ∈ J ^ r := by
  sorry

end AddMonoidAlgebra
