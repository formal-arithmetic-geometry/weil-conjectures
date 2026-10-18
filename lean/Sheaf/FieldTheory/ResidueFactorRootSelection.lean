/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Selecting a root of an irreducible factor that avoids another polynomial

Source: Stacks Project, Algebra, Tag 00UF, proof of
`lemma-standard-etale-finite-flat-Zariski`, final residue-field paragraph
(blueprint: lem-trf-residue-factor-root-selection).
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace Polynomial

/-- An irreducible factor of a monic polynomial with a prescribed finite linear factorization
has a root in that family at which any polynomial not divisible by the factor is nonzero.
The family may be empty, and the irreducible factor is only required to be irreducible over
`k`, not over `L`.

Source: Stacks Project, Algebra, Tag 00UF, proof of
`lemma-standard-etale-finite-flat-Zariski`, final residue-field paragraph
(blueprint: lem-trf-residue-factor-root-selection).

Proof plan:
1. The field map is injective (`def-pc-field-extension`). Irreducibility makes `f₁`
   nonzero and nonconstant, and its coefficient image stays nonconstant. Monicity makes
   `f` nonzero (`def-weil-polynomial-ring`).
2. The polynomial ring over `k` is a PID (`lem-pur-polynomial-field-pid`). A generator
   of the ideal of combinations `A * f₁ + B * g` divides both `f₁` and `g`.
   Irreducibility and `¬ f₁ ∣ g` make this generator a unit, yielding a Bezout identity
   `A * f₁ + B * g = 1` over `k`.
3. Coefficient extension is an injective ring homomorphism
   (`lem-weil-coefficientwise-extension-injective`). Thus the nonconstant image of `f₁`
   divides the nonzero split image of `f`, and splits by
   `lem-trf-divisor-of-split-polynomial`.
4. This nonconstant split polynomial has a root `β`. Since `f₁ ∣ f`, evaluation
   (`def-weil-polynomial-root`) gives `f(β) = 0`. Evaluating the prescribed product
   gives a zero product of `β - α i`, so some factor vanishes and `β = α i`.
   An empty family would instead give `0 = 1`, so is impossible under the hypotheses.
5. Evaluate the Bezout identity at this same `α i`. Its first term vanishes, giving
   `B(α i) * g(α i) = 1`, hence `g(α i) ≠ 0`.
-/
theorem exists_index_eval₂_eq_zero_and_ne_zero
    {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]
    (f g : k[X]) (hf : f.Monic) {I : Type w} [Fintype I] (α : I → L)
    (hfactor : f.map (algebraMap k L) = ∏ i : I, (X - C (α i)))
    (f₁ : k[X]) (hf₁ : Irreducible f₁) (hdiv : f₁ ∣ f) (hnotdiv : ¬ f₁ ∣ g) :
    ∃ i : I, f₁.eval₂ (algebraMap k L) (α i) = 0 ∧
      g.eval₂ (algebraMap k L) (α i) ≠ 0 := by
  sorry

end Polynomial
