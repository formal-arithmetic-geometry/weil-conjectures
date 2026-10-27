module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A common good section for two surjections over a field

Source: Stacks Project, More on Algebra, Tag 0FJK (`lemma-homotopic-surjections`),
final paragraph, the field common-complement assertion
(blueprint: lem-trf-field-common-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace LinearMap

/-- Two surjections between coordinate vector spaces admit a right inverse of the first
whose composite with the second is a linear isomorphism. No infinitude assumption on the
field or positivity assumption on the coordinate counts is needed.

Source: Stacks Project, Tag 0FJK (`lemma-homotopic-surjections`), final paragraph
(blueprint: lem-trf-field-common-section).

Proof in words:
1. Put `V = k^n`, `W = k^m`, `P = ker a`, and `Q = ker b`. Standard coordinate
   vectors span the coordinate spaces. By [lem-trf-vector-subspace-complement], projection
   onto any subspace along a complement shows that it too is finitely spanned. Rank-nullity
   [lem-weil-pbc-idempotent-charpoly-rank-nullity] and surjectivity give
   `dim W + dim P = dim V = dim W + dim Q`, hence `dim P = dim Q`.
2. Put `I = P ∩ Q`. Choose complements `P = I ⊕ P₁` and `Q = I ⊕ Q₁` using
   [lem-trf-vector-subspace-complement] inside each kernel. Rank-nullity for their
   projections onto `I` gives `dim P₁ = dim Q₁`. Also `P + Q = I ⊕ P₁ ⊕ Q₁`:
   if `i + x + y = 0`, then `y ∈ P ∩ Q₁ = 0`, and then `i = x = 0`.
3. By [lem-trf-equal-dimension-linear-equivalence], choose an isomorphism `e : P₁ → Q₁`.
   Its graph `D = {x + e(x) | x ∈ P₁}` meets each of `P` and `Q` trivially. Moreover,
   `P + D = P + Q = Q + D`, since `y = (e⁻¹(y) + y) - e⁻¹(y)` for `y ∈ Q₁`, and
   `x = (x + e(x)) - e(x)` for `x ∈ P₁`.
4. Choose a complement `R` of `P + Q` in `V` by [lem-trf-vector-subspace-complement].
   Then `U = D + R` complements both `P` and `Q` in `V`. Indeed, both sums generate `V`;
   if `d + r` belongs to either kernel, then `r ∈ (P + Q) ∩ R = 0`, and then `d = 0`.
5. The restrictions of `a` and `b` to `U` are injective by these trivial intersections,
   and surjective by decomposing a lift in `P ⊕ U` or `Q ⊕ U`. Define `q` as the inverse
   of `a|U` followed by inclusion into `V`. Uniqueness of lifts in `U` proves linearity
   and `a ∘ q = id`; `b ∘ q` is bijective with linear inverse `a|U ∘ (b|U)⁻¹`.
   When `m = 0` the assertion concerns the zero space; `n = 0` forces `m = 0`.
   Only addition, subtraction, and linear isomorphisms were used, including in
   characteristic two and over finite fields. -/
theorem exists_common_section_of_surjective (k : Type u) [Field k] (m n : ℕ)
    (a b : (Fin n → k) →ₗ[k] (Fin m → k))
    (ha : Function.Surjective a) (hb : Function.Surjective b) :
    ∃ q : (Fin m → k) →ₗ[k] (Fin n → k),
      a.comp q = LinearMap.id ∧ Function.Bijective (b.comp q) := by
  sorry

end LinearMap
