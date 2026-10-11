/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.FieldTheory.SeparableExtension
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A separable extension as the fraction field of a smooth algebra

Source: Stacks Project, Algebra, Lemma Tag 037X (lemma-localization-smooth-separable),
implication “separable => localization of a smooth k-algebra” (blueprint:
lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra).
-/

universe u v

namespace FieldTheory

/-- Let `K/k` be a field extension finitely generated as a field (`(⊤ : IntermediateField k K).FG`)
and separable. There is a `k`-subalgebra `B` of `K` such that `k → B` is smooth and `K` is the
fraction field of `B` (`IsFractionRing B K`: every element of `K` is `b/b'` with `b, b' ∈ B`,
`b' ≠ 0`).
Source: Stacks Project, Algebra, Lemma Tag 037X (lemma-localization-smooth-separable),
implication “separable => localization of a smooth k-algebra”.
(blueprint: lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra). The proof first
chooses a
finite-type domain with fraction field `K`, applies smoothness at the generic point, and then
localizes at a nonzero element.
-/
theorem exists_smooth_subalgebra_fraction_field
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) (hsep : Algebra.IsSeparableExtension k K) :
    ∃ B : Subalgebra k K,
      Algebra.Smooth k B ∧ IsFractionRing B K := by
  sorry

end FieldTheory
