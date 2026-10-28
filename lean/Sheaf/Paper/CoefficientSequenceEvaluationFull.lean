/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E6
-/
module

public import Sheaf.Paper.CoefficientRingedSequenceSite

/-! # Fullness of derived evaluation on quotient coefficient sequences

Source: Stacks 0941, 079P, 07A6, and the coinduced sequence resolution described below.
(blueprint: lem-coef-sequence-derived-evaluation-full).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

/-- Compatible morphisms of finite evaluations lift to a morphism of derived
quotient systems. No uniqueness or detection of equality is asserted.

Source: Stacks, Cohomology on Sites, 0941; Injectives, 079P; Cohomology on Sites, 07A6.
The two-term coinduced resolution is the agent-expanded sequential descent argument
for prop-coef-integral-dualizing, paragraph 2.
(blueprint: lem-coef-sequence-derived-evaluation-full).

Proof: use the equivalence between modules on the vertical ringed sequence site
and sequences M_n with arrows M_(n+1) to Res(M_n). Write r_n for the right adjoint
of evaluation at n: its level m is zero for m<n and restriction of M_n for m>=n.
Restriction of scalars is exact, so r_n is exact. For a complex N there is a
short exact sequence of complexes
  0 -> N -> product_n r_n(N_n) -> product_n r_(n+1)(Res(N_n)) -> 0.
At level m the products have only m+1 and m factors. The first map lists all
transitions from level m; the second subtracts consecutive transition composites.
Its kernel is N_m, and one solves for its m target coordinates recursively, so
it is surjective. All these products are locally finite; their formation is exact.
Each r_n is right adjoint to exact evaluation, and thus preserves K-injectives.
Resolve the entries N_n of the first product, and resolve Res(N_n) independently
for the second product; restriction itself need not preserve K-injectives.
Products of the resulting coinduced K-injectives are K-injective. Because every
level sees only finitely many factors, these replacements are quasi-isomorphisms.
The displayed short exact sequence therefore gives a distinguished triangle with
first object N and the two derived coinduced products as its other objects.
Under the derived adjunctions a map from M to the first product is precisely a
family f_n of derived maps M_n to N_n. Its composite with the difference map is
zero precisely when f_(n+1) followed by the target transition equals the source
transition followed by Res(f_n). The hypothesis supplies these equations. Exactness
of Hom(M,-) on the distinguished triangle gives the required map M to N, and its
composite with the first arrow gives the stated evaluation equations.
This argument uses exact restriction, never flatness of the quotient map or
preservation of K-injectives by evaluation. It applies to unbounded complexes,
zero objects, the empty scheme, and identity quotient transitions. -/
theorem coefficientSequenceDerivedEvaluation_full
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
    (M N : coefficientSequenceDerived l E W)
    (f : ∀ n : ℕ, (coefficientSequenceDerivedEvaluation l E W n).obj M ⟶
      (coefficientSequenceDerivedEvaluation l E W n).obj N)
    (hf : ∀ n : ℕ,
      f (n + 1) ≫ (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app N =
        (coefficientSequenceDerivedTransition l E W (Nat.le_succ n)).app M ≫
          (normalizedDVRRes l E W (Nat.le_succ n)).map (f n)) :
    ∃ g : M ⟶ N, ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation l E W n).map g = f n := by sorry

end WeilConjectures
