module

public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Minimal-support coordinates of a fixed vector

Source: Stacks Project, Algebra, Tag 0592, `lemma-projective-freeness-criteria`,
first and second paragraphs of the proof and the final coefficient comparison
(blueprint: lem-trf-minimal-support-fixed-vector-coordinates).
-/

@[expose] public section

universe u v

namespace Module.Free

/-- A nonzero vector fixed by a linear endomorphism admits a basis expansion with
least support, irredundant coefficients, and compatible endomorphism coordinates.

Source: Stacks Project, Algebra, Tag 0592, `lemma-projective-freeness-criteria`,
first and second proof paragraphs and the coefficient comparison in the last paragraph
(blueprint: lem-trf-minimal-support-fixed-vector-coordinates).

Proof:
1. By def-weil-pbc-free-module, a basis gives a unique finitely supported expansion.
   Minimize its support cardinality over all bases, and enumerate the minimizing
   support by `Fin n`. Since `x` is nonzero, `n` is positive and its coefficients
   are nonzero. Bases may be reindexed by their ranges in `F`, so index universe
   `v` loses no basis or support cardinality.
2. If `a j` were a combination of the other coefficients, replace each selected
   basis vector `B (e i)`, for `i ≠ j`, by `B (e i) + c i • B (e j)`.
   Fix all other basis vectors. The inverse change subtracts these multiples;
   the two finite coefficient formulas give inverse expansions, hence a basis.
3. In the new basis the `j`th coefficient of `x` is zero and the others are
   unchanged, contradicting minimality. Thus the coefficients are irredundant.
4. Expand each `π (B (e i))` in the minimizing basis. Separate the selected
   coefficients `b i j` from the remaining finite sum `t i`, which belongs to
   the span of the complementary basis vectors. Applying `π` to the expansion
   of `x` and using linearity and `hπ` gives the second expansion of `x`.
5. Each `t i` has zero selected coordinates. Substitute the expansions of the
   images into the second expansion of `x` and compare its unique coordinates
   to obtain `a j = ∑ i, a i * b i j`. All sums are finite; no finite-generation
   assumption on `F` is used.
-/
theorem exists_minimal_support_fixed_vector_coordinates
    {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F] [Module R F]
    [Module.Free R F] (x : F) (hx : x ≠ 0) (π : F →ₗ[R] F) (hπ : π x = x) :
    ∃ (ι : Type v) (B : Module.Basis ι R F) (n : ℕ) (e : Fin n → ι)
      (a : Fin n → R),
      1 ≤ n ∧
      Function.Injective (fun i ↦ B (e i)) ∧
      (∀ i, a i ≠ 0) ∧
      x = ∑ i : Fin n, a i • B (e i) ∧
      (B.repr x).support.card = n ∧
      (∀ (κ : Type v) (C : Module.Basis κ R F), n ≤ (C.repr x).support.card) ∧
      (∀ j : Fin n, ¬ ∃ c : Fin n → R,
        a j = ∑ i ∈ Finset.univ.erase j, a i * c i) ∧
      ∃ (b : Fin n → Fin n → R) (t : Fin n → F),
        (∀ i, t i ∈ Submodule.span R (B '' (Set.range e)ᶜ)) ∧
        (∀ i, π (B (e i)) = (∑ j : Fin n, b i j • B (e j)) + t i) ∧
        x = ∑ i : Fin n, a i • π (B (e i)) ∧
        ∀ j : Fin n, a j = ∑ i : Fin n, a i * b i j := by
  sorry

end Module.Free
