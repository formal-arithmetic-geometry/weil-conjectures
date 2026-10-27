module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# PBW for an arbitrary-dimensional rational Lie algebra

Source: Milne, Algebraic Groups (2017), Section 10j, Theorem 10.36, printed pp. 199–204
(blueprint: lem-sfb-arbitrary-basis-pbw).

The enveloping algebra and its canonical map are Mathlib's tensor-algebra quotient and
`UniversalEnvelopingAlgebra.ι`. Nondecreasing finite lists index the ordered monomials.
The total order need not be a well-order. No finiteness assumption is imposed; the index
set may be empty and the Lie algebra may be zero. The zero Lie algebra has empty basis
index set, and its
canonical scalar map identifies its enveloping algebra with the rational numbers.
-/

@[expose] public section

universe u v

namespace UniversalEnvelopingAlgebra

/-- Every totally ordered rational basis, of arbitrary cardinality, gives the ordered
monomial basis of the enveloping algebra. The canonical Lie map is injective. For the
zero Lie algebra the only ordered word is empty, and the scalar map is bijective.
Source: Milne, Algebraic Groups (2017), Section 10j, Theorem 10.36, printed pp. 199–204
(blueprint: lem-sfb-arbitrary-basis-pbw).

Proof plan:
1. Use `lem-sfb-tensor-word-basis` (`Module.Basis.tensorAlgebra`) to identify the tensor
   algebra with the vector space on finite words. For `r(x,y) = xy - yx - ⁅x,y⁆`,
   bilinearity and alternation (`def-wf-lie-algebra`) show that the defining ideal is
   the vector span of contextual relations `A r(a,b) C` for basis letters `a > b`.
   Expand both multipliers in the word basis; this span is closed under multiplication.
2. Rank words by the lexicographic pair (length, number of inversions) in `ℕ × ℕ`.
   This gives a well-founded strict partial order even when the alphabet's total order
   is not well founded. The rule `AabC ↦ A(ba + ⁅a,b⁆)C` for `a > b` lowers the rank:
   swapping lowers the inversion count by one, and each bracket word is shorter.
3. Rules at the same position agree. For disjoint inversions in `AabCuvD`, put
   `p = ba + ⁅a,b⁆`, `q = vu + ⁅u,v⁆`, and compare both first reducts with `ApCqD`.
   Their differences are `ApC r(u,v)D` and `A r(a,b)CqD`. Expand the bracket terms.
   Every resulting relation has smaller leading word: another inversion was swapped,
   or a bracket shortened the word. This also covers an empty intervening word `C`.
4. Overlapping inversions have three letters `a > b > c`. Continuing the two reductions
   gives `P = cba + ⁅b,c⁆a + b⁅a,c⁆ + ⁅a,b⁆c` and
   `Q = cba + c⁅a,b⁆ + ⁅a,c⁆b + a⁅b,c⁆`. The intermediate leading words are
   `bac`, `bca`, `acb`, `cab`, each with fewer inversions than `abc`. Restoring a
   fixed prefix and suffix preserves this comparison, since the multiset is unchanged.
5. Expand `P - Q` as `r(⁅b,c⁆,a) + r(b,⁅a,c⁆) + r(⁅a,b⁆,c)` plus
   `⁅⁅b,c⁆,a⁆ + ⁅b,⁅a,c⁆⁆ + ⁅⁅a,b⁆,c⁆`. The latter sum vanishes by skew symmetry
   and Jacobi (`def-wf-lie-algebra`). Step 1 expands the remaining three relations
   into basis relations whose contextual leading words are shorter. Thus all pairs of
   rules with the same leading word agree modulo strictly smaller relations.
6. Apply `lem-sfb-triangular-linear-relations` to these contextual rules. The relation
   span is exactly the defining ideal by Step 1. Irreducible words are exactly the
   nondecreasing lists, by transitivity of the total order. Their quotient classes
   give the displayed basis. The empty list has product one.
7. The one-letter words are distinct members of this basis, so a finite basis expansion
   of an element in the kernel of `ι` has all coefficients zero. To obtain injectivity
   for any `L` without a supplied basis, use `lem-weil-pbc-vector-space-free`
   (`Module.Free.of_divisionRing`) and choose a total order on its basis index set.
   If `L` is zero, no basis vector can exist. The alphabet is empty, the sole word
   is empty, and the basis consists of one. Hence the canonical scalar map is bijective.
-/
theorem exists_arbitrary_basis_pbw (L : Type u) [LieRing L] [LieAlgebra ℚ L] :
    (∀ (B : Type v) [LinearOrder B] (e : Module.Basis B ℚ L),
      ∃ E : Module.Basis {w : List B // w.Pairwise (fun a b : B ↦ a ≤ b)} ℚ
          (UniversalEnvelopingAlgebra ℚ L),
        (∀ w : {w : List B // w.Pairwise (fun a b : B ↦ a ≤ b)},
          E w = (w.val.map (fun b ↦ ι ℚ (e b))).prod) ∧
        (Subsingleton L → IsEmpty B)) ∧
    Function.Injective (ι ℚ : L → UniversalEnvelopingAlgebra ℚ L) ∧
    (Subsingleton L →
      Function.Bijective (algebraMap ℚ (UniversalEnvelopingAlgebra ℚ L))) := by
  sorry

end UniversalEnvelopingAlgebra
