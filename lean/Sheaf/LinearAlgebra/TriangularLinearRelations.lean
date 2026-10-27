/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.RelClasses

/-!
# A quotient basis from well-founded triangular linear relations

Source: Milne, Algebraic Groups (2017), Theorem 10.36, printed pp. 201--204,
Steps 4--8. This abstract criterion is the agent-written supporting normal-form
argument, not a theorem stated in Milne (blueprint: lem-sfb-triangular-linear-relations).
-/

@[expose] public section

universe u v w

namespace Module.Basis

/-- The unreduced coordinate classes form a basis modulo compatible triangular relations.

Source: the agent-written linear normal-form criterion supporting Milne, Algebraic Groups
(2017), Theorem 10.36, printed pp. 201--204, Steps 4--8
(blueprint: lem-sfb-triangular-linear-relations).

Proof:
1. Put `N = W ∖ Set.range leading` and `V = N →₀ k`, and extend by zero via `i : V → F`.
   For each reducible `w`, choose a rule `s_w` leading at `w`. Using
   `IsWellFounded.fix` and `IsWellFounded.fix_eq` from
   `lem-sfb-well-founded-relation-recursion`, define `g(w)` to be the coordinate vector
   at `w` if `w ∈ N`, and otherwise the sum of `f(s_w)(v) • g(v)` over its finite support.
   The support condition ensures that every recursive argument is a predecessor.
2. Define the linear map `P : F → V` by summing `a(w) • g(w)` over the support of `a`.
   Linearity follows by taking unions of finite supports and inserting zero terms.
   Then `P(e_w) = g(w)` and `P ∘ i = id`.
3. By `IsWellFounded.induction` from `lem-sfb-well-founded-relation-recursion`, prove
   `g(w) = P(f(s))` for every rule leading at `w`. The induction hypothesis says that
   `P` kills every generator of `R_{≺w}`, hence that subspace. Compatibility makes
   `P(f(s)) = P(f(s_w)) = g(w)`. Thus `P` kills all generators of `R` and kills `R`.
4. By the same well-founded induction, prove `e_w - i(g(w)) ∈ R`. This is zero for
   `w ∈ N`. Otherwise it equals `e_w - f(s_w)` plus the finite sum of
   `f(s_w)(v) • (e_v - i(g(v)))`; all terms lie in `R` by the support hypothesis and
   induction. Summing gives `a - i(P(a)) ∈ R` for every `a`.
5. The previous identity shows that the specified quotient classes span. If `i(b) ∈ R`,
   applying `P` gives `b = 0`, so the classes are linearly independent. They therefore
   form the asserted basis, including the empty-index and empty-rule cases. -/
theorem exists_basis_quotient_of_wellFounded_triangular_relations
    {k : Type u} [Field k] {W : Type v} {S : Type w}
    (r : W → W → Prop) [IsStrictOrder W r] (hwf : WellFounded r)
    (leading : S → W) (f : S → W →₀ k)
    (hsupport : ∀ s : S, ↑(f s).support ⊆ {v : W | r v (leading s)})
    (hcompat : ∀ (w : W) (s t : S), leading s = w → leading t = w →
      f s - f t ∈ Submodule.span k
        {a : W →₀ k | ∃ q : S, r (leading q) w ∧
          a = Finsupp.single (leading q) 1 - f q}) :
    ∃ b : Module.Basis {n : W // n ∉ Set.range leading} k
      ((W →₀ k) ⧸ Submodule.span k
        (Set.range (fun s : S => Finsupp.single (leading s) 1 - f s))),
      ∀ n : {n : W // n ∉ Set.range leading},
        b n = Submodule.Quotient.mk (Finsupp.single n.val 1) := by
  sorry

end Module.Basis
