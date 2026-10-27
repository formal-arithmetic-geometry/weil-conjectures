module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Rigidity of an algebraic field tower with one rational endpoint

Source: Stacks Project, Tags 09GQ and 09GR, and the two-alternative tower argument
extracted from Step 3 of `lem-trf-etale-completed-local-ring-iso`
(blueprint: lem-trf-algebraic-field-tower-rationality).
-/

@[expose] public section

universe u v w

namespace IsAlgClosed

/-- If `k` is algebraically closed and `L` is algebraic over `K` through `α`, bijectivity
of either `i` or `α.comp i` forces all three specified maps to be bijective.

Source: Stacks Project, Tags 09GQ (definition-algebraically-closed) and 09GR
(lemma-algebraically-closed), applied to the two-alternative tower argument from
Step 3 of `lem-trf-etale-completed-local-ring-iso`
(blueprint: lem-trf-algebraic-field-tower-rationality).

Proof plan:
1. Every unital homomorphism of fields is injective (`def-pc-field-extension`): a
   nonzero element in its kernel would give `1 = 0` by applying the homomorphism
   to the product of that element and its inverse. Thus only surjectivity remains.
2. If `i` is bijective, lift each coefficient of a nonzero polynomial over `K`
   annihilating `z : L` through `i`. The resulting polynomial over `k` is nonzero
   and vanishes at `z` through `α.comp i`. Apply
   `lem-weil-pbc-algebraic-over-algebraically-closed-subfield`, using
   `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic` on the relative
   algebraic closure, to obtain `z = α (i a)` for some `a : k`. This proves
   surjectivity of both the composite and `α`.
3. If `α.comp i` is bijective, each `z : L` is `α (i a)` for some `a : k`, so `α`
   is surjective. For `b : K`, choose `a : k` with `α (i a) = α b`; injectivity
   of `α` gives `i a = b`. Hence `i` is also surjective. This case does not use
   algebraicity or algebraic closedness. Combine these with step 1. -/
theorem bijective_field_tower_of_bijective_or_comp
    {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [IsAlgClosed k] (i : k →+* K) (α : K →+* L)
    (halg : ∀ z : L, ∃ p : Polynomial K, p ≠ 0 ∧ p.eval₂ α z = 0)
    (hbij : Function.Bijective i ∨ Function.Bijective (α.comp i)) :
    Function.Bijective i ∧ Function.Bijective (α.comp i) ∧ Function.Bijective α := by
  sorry

end IsAlgClosed
