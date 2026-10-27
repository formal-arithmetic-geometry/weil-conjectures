module

public import Sheaf.GroupTheory.GeneratorWordLength
public import Mathlib.Data.Finite.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Deletion and shortest representatives of parabolic cosets

Source: Cashen, Notes on Coxeter groups (31 October 2023), Chapter 4,
Lemma 4.0.5 (Bridge Lemma), printed p.118, and Lemma 4.0.14(2), pp.120–121.
Only the deletion argument is used; no Coxeter presentation is assumed.
(blueprint: lem-sfb-deletion-parabolic-coset-length)
-/

@[expose] public section

universe u v

namespace Monoid

/-- Deletion preserves the restricted word metric and makes multiplication by a
shortest representative of a left parabolic coset length additive.
Source: Cashen, Notes on Coxeter groups, Chapter 4, Lemmas 4.0.5 and 4.0.14(2).

Proof:
1. Products of words in `J` contain `1`, multiply by concatenation, and invert by
reversing words, since the letters are involutions. Thus they form exactly
`Subgroup.closure (t '' J)`. Generation gives words for every element of `G`, and
least lengths exist in the natural numbers.
2. Choose a shortest `J`-word for `u`. If it is not shortest in the full alphabet,
deletion shortens it by two letters while keeping it a `J`-word, a contradiction.
Hence the restricted and ambient lengths coincide.
3. Choose a shortest `J`-word `A` for `u` and a shortest word `B` for `h`. Their
concatenation represents `u * h`, so its length is an upper bound. If not minimal,
apply deletion to this concatenation.
4. Two deletions in `A` contradict its minimality after right cancellation of `h`.
Two deletions in `B` contradict its minimality after left cancellation of `u`.
5. In the mixed case the remaining words `A₁`, `B₁` satisfy
`t_{B₁} = t_{A₁}⁻¹ * u * h`. The left multiplier lies in the subgroup. Minimality
of `h` forces `length h ≤ length t_{B₁} ≤ length B - 1`, a contradiction.
Thus the concatenation is minimal and its length is the asserted sum.
(blueprint: lem-sfb-deletion-parabolic-coset-length) -/
theorem deletion_parabolic_coset_length {G : Type u} [Group G] {I : Type v} [Finite I]
    (t : I → G) (hinj : Function.Injective t) (hne : ∀ i : I, t i ≠ 1)
    (hinvol : ∀ i : I, t i ^ 2 = 1) (hgen : Subgroup.closure (Set.range t) = ⊤)
    (hdelete : ∀ A : List I, generatorWordLength t (A.map t).prod < A.length →
      ∃ a b : ℕ, a < b ∧ b < A.length ∧
        (((A.eraseIdx b).eraseIdx a).map t).prod = (A.map t).prod)
    (J : Set I) :
    (∀ u : G, u ∈ Subgroup.closure (t '' J) →
      generatorWordLength (fun j : J ↦ t j) u = generatorWordLength t u) ∧
    (∀ h : G, (∀ v : G, v ∈ Subgroup.closure (t '' J) →
      generatorWordLength t h ≤ generatorWordLength t (v * h)) →
      ∀ u : G, u ∈ Subgroup.closure (t '' J) →
        generatorWordLength t (u * h) =
          generatorWordLength (fun j : J ↦ t j) u + generatorWordLength t h) := by
  sorry

end Monoid
