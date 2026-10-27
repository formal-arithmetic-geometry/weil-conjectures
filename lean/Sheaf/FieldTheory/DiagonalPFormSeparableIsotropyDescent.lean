module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Separable

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Separable descent of isotropy for diagonal p-forms

Source: Brian Conrad, *The structure of solvable groups over general fields*,
Lemma 1.12, printed p.7, with the finite Galois reduction recorded in the DAG
(blueprint: lem-sfb-diagonal-p-form-separable-isotropy-descent).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A diagonal p-form with arbitrary nonnegative Frobenius exponents has a nonzero
zero over the base field if it has one over a separable algebraic extension.
Zero coefficients and unequal exponents are permitted.

Source: Conrad, *The structure of solvable groups over general fields*, Lemma 1.12,
printed p.7 (blueprint: lem-sfb-diagonal-p-form-separable-isotropy-descent).

Proof plan from the DAG:
1. Embed the extension into a separable closure, using
   lem-weil-pbc-separable-closure-exists-galois and
   lem-weil-pbc-separable-extension-embeds-separably-closed. By
   lem-weil-pbc-finite-set-in-finite-galois-subextension, the coordinates lie in a
   finite Galois subextension; embeddings preserve the equation and nonvanishing.
2. Induct strongly on the number of terms. For one term, its coefficient must be
   zero, so the coordinate 1 works. A zero coordinate permits deletion and induction.
3. Otherwise choose a maximal exponent m_j and normalize by
   x_i = a_i / a_j ^ (p ^ (m_j - m_i)). Then x_j = 1 and the equation persists.
   If all normalized coordinates belong to the base, they give the desired tuple.
4. Otherwise lem-weil-pbc-finite-galois-fixed-field supplies an automorphism moving
   one coordinate. The differences x_i - sigma(x_i) solve the same equation by the
   Frobenius subtraction identity of def-weil-ring-frobenius, are not all zero,
   and vanish at j. Delete j, apply induction, and reinsert zero. -/
theorem exists_nonzero_diagonal_p_form_zero_of_isSeparable
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] (p : ℕ) (hp : p.Prime) [CharP k p]
    (n : ℕ) (hn : 1 ≤ n) (c : Fin n → k) (m : Fin n → ℕ)
    (h : ∃ a : Fin n → L, a ≠ 0 ∧
      ∑ i : Fin n, algebraMap k L (c i) * (a i) ^ (p ^ (m i)) = 0) :
    ∃ b : Fin n → k, b ≠ 0 ∧ ∑ i : Fin n, c i * (b i) ^ (p ^ (m i)) = 0 := by
  sorry

end Algebra
