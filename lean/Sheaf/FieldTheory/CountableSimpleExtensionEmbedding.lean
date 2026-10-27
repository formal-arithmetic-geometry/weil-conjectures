module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.AlgebraicCard

/-! # Embeddings of countable simple field extensions

Source: Stacks Project, Fields, Tags 09G1, 09GK, 09GN and 09GU
(blueprint: lem-sfb-countable-simple-extension-embedding).
-/

@[expose] public section

universe u v w

namespace IntermediateField

/-- A simple extension of a countable field is countable, and an embedding of its base
into an uncountable algebraically closed field extends to it.

Source: Stacks Project, Fields, Tags 09G1, 09GK, 09GN and 09GU
(blueprint: lem-sfb-countable-simple-extension-embedding).

Proof plan:
1. The subfield of rational expressions `P(a) / Q(a)`, with `Q(a) ≠ 0`, contains the
   base field and `a`, and is contained in every subfield containing them. It is therefore
   `adjoin E {a}`; polynomial evaluation uses `def-weil-polynomial-ring`.
2. Encode polynomials by finite lists of coefficients, using countability of `E`.
   Polynomial pairs are countable. Assign to each element of `adjoin E {a}` the least code
   of a representing pair to obtain countability, even for finite `E` or `a` in the base.
3. If `a` is algebraic, `lem-weil-pbc-simple-algebraic-extension-power-basis` gives a finite
   basis. Linear dependence of sufficiently many powers makes every element algebraic
   (`def-weil-algebraic-element`).
4. Apply `lem-weil-pbc-algebraic-extension-embeds-algebraically-closed`, namely
   `IsAlgClosed.lift`, with the target algebra structure induced by `τ`. Its underlying
   field homomorphism extends `τ` and is injective.
5. Otherwise, `lem-sfb-algebraic-elements-countable` (`Algebraic.countable`) shows that
   the elements of `Ω` algebraic over `E` via `τ` form a countable set. Uncountability
   supplies a transcendental element `b`; no nonzero polynomial over `E` vanishes at it.
6. Send `P(a) / Q(a)` to the quotient evaluated at `b`, applying `τ` to coefficients.
   Equality of source quotients implies that the cross-multiplied polynomial is zero,
   since `a` is transcendental. Evaluation at `b` gives well-definedness. The quotient
   formulas give preservation of addition, multiplication and one; constants map by `τ`.
   Transcendence of `b` gives a trivial kernel, hence an embedding extending `τ`.
-/
theorem countable_adjoin_simple_and_exists_embedding
    {E : Type u} {L : Type v} {Ω : Type w}
    [Field E] [Field L] [Field Ω] [Algebra E L] [Countable E]
    [IsAlgClosed Ω] [Uncountable Ω] (a : L) (τ : E →+* Ω) :
    Countable (adjoin E {a}) ∧
      ∃ τ' : adjoin E {a} →+* Ω, ∀ x : E,
        τ' (algebraMap E (adjoin E {a}) x) = τ x := by
  sorry

end IntermediateField
