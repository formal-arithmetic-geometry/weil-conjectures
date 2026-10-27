module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.List.FinRange
import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
# Filtered PBW over an arbitrary field

Source: Milne, Algebraic Groups (2017), Theorem 10.36, printed pp. 200–204
(blueprint: lem-sfb-field-filtered-pbw).

The quotient and its generator map are Mathlib's `UniversalEnvelopingAlgebra` and
`UniversalEnvelopingAlgebra.ι`. Ordered products use `List.finRange`, since the enveloping
algebra need not be commutative. The filtered subspace is the span of words of bounded length.
-/

@[expose] public section

universe u v

namespace UniversalEnvelopingAlgebra

/-- Ordered monomials form a basis, and those of total degree at most `d` form a basis of
words of length at most `d`. If the given basis is empty, the scalar map is an isomorphism.
Source: Milne, Algebraic Groups (2017), Theorem 10.36, printed pp. 200–204
(blueprint: lem-sfb-field-filtered-pbw).

Proof plan:
1. Use `lem-sfb-tensor-word-basis` (`Module.Basis.tensorAlgebra`) to identify the tensor
   algebra with the word coordinate space. Bilinearity and alternation from
   `def-wf-lie-algebra` show that the defining ideal is the span of contextual relations
   `A (ab - ba - ⁅a, b⁆) B` for basis letters `a > b`.
2. Order words by length and then lexicographically. This order is well founded for the
   finite alphabet and preserved by a common prefix and suffix. Replacing an adjacent
   inversion `ab` by `ba + ⁅a, b⁆` strictly lowers this order and never increases length.
3. Reductions at the same position agree. For disjoint inversions in `AabBuvC`, put
   `p = ba + ⁅a, b⁆` and `q = vu + ⁅u, v⁆`. Compare both first reducts with `ApBqC`.
   The differences are contextual relations whose leading words are strictly smaller,
   because the other pair is swapped or replaced by a bracket. Empty intervening words
   are allowed.
4. For the overlap `abc` with `a > b > c`, reducing the left pair and then its remaining
   inversions gives `cba + ⁅b, c⁆a + b⁅a, c⁆ + ⁅a, b⁆c`. Reducing the right pair gives
   `cba + c⁅a, b⁆ + ⁅a, c⁆b + a⁅b, c⁆`. All intermediate cubic leading words are
   smaller than `abc`, also after restoring a fixed prefix and suffix.
5. Write `r(x,y) = xy - yx - ⁅x,y⁆`. The difference in Step 4 is
   `r(⁅b,c⁆,a) + r(b,⁅a,c⁆) + r(⁅a,b⁆,c)` plus the Jacobi sum
   `⁅⁅b,c⁆,a⁆ + ⁅b,⁅a,c⁆⁆ + ⁅⁅a,b⁆,c⁆`, which vanishes. Bilinearity expands each
   remaining relation in basis relations of shorter leading length. Thus every ambiguity
   agrees modulo strictly smaller relations. Alternation gives skew symmetry without
   division by two, so this argument includes characteristic two.
6. Apply `lem-sfb-triangular-linear-relations` to the word coordinate space and these rules.
   Its relation span is the defining ideal. Irreducible words are exactly nondecreasing
   words, uniquely indexed by `Fin n → ℕ`. Their quotient classes give the first basis.
7. For each `d`, expand products of at most `d` vectors in the given basis. Induction on
   the word order reduces them to nondecreasing words of length at most `d`, because
   reductions never increase length. Conversely those ordered words are products of at
   most `d` vectors. They are independent as a subfamily of the first basis. This gives
   the displayed basis of the filtered subspace, including `d = 0`.
8. If `n = 0`, there are no letters or relations. The only word is empty, its class is
   one, and the scalar map from the field to its enveloping algebra is bijective. -/
theorem exists_field_filtered_pbw_basis
    (F : Type u) [Field F] (L : Type v) [LieRing L] [LieAlgebra F L]
    (n : ℕ) (e : Module.Basis (Fin n) F L) :
    ∃ B : Module.Basis (Fin n → ℕ) F (UniversalEnvelopingAlgebra F L),
      (∀ m : Fin n → ℕ,
        B m = ((List.finRange n).map (fun i ↦ ι F (e i) ^ m i)).prod) ∧
      (∀ d : ℕ,
        ∃ Bd : Module.Basis {m : Fin n → ℕ // ∑ i, m i ≤ d} F
            (Submodule.span F {z : UniversalEnvelopingAlgebra F L |
              ∃ xs : List L, xs.length ≤ d ∧ (xs.map (fun x ↦ ι F x)).prod = z}),
          ∀ m : {m : Fin n → ℕ // ∑ i, m i ≤ d},
            (Bd m : UniversalEnvelopingAlgebra F L) = B m.val) ∧
      (n = 0 → Function.Bijective (algebraMap F (UniversalEnvelopingAlgebra F L))) := by
  sorry

end UniversalEnvelopingAlgebra
