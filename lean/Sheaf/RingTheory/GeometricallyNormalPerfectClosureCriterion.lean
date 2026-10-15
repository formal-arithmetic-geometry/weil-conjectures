/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.FieldTheory.MakeSeparable
import Sheaf.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import Sheaf.RingTheory.SmoothNormalRing
import Sheaf.RingTheory.FilteredColimitNormalRing
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Perfect-closure criterion for geometric normality

Source: Stacks Project, Algebra, Tag 037Z (lemma-geometrically-normal), (4) iff (1),
and Tag 046W (lemma-perfection)
(blueprint: lem-weil-pbc-geometrically-normal-perfect-closure-criterion).
-/

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Algebra

/-- Normality after extension to a perfect closure is equivalent to normality after every
field extension, with no finiteness or nonzero assumption on the algebra.

Source: Stacks Project, Algebra, Tag 037Z (lemma-geometrically-normal), (4) iff (1),
and Tag 046W (lemma-perfection).
(blueprint: lem-weil-pbc-geometrically-normal-perfect-closure-criterion).

Proof:
1. The reverse implication specializes to the perfect closure. In characteristic zero the
   power condition identifies P with k; in positive characteristic Frobenius on P is bijective.
2. Each finite purely inseparable extension k₁/k embeds in P by sending an element to its unique
   iterated Frobenius root. Uniqueness makes this a field homomorphism. Tensor associativity
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) and normality descent
   (lem-weil-pbc-normal-ring-field-extension-descent) give normality of k₁ ⊗[k] A.
3. For a finitely generated K/k, lem-weil-pbc-make-separable supplies k₁ and K₁ with finite
   purely inseparable horizontal extensions and K₁/k₁ separable. It is still finitely generated,
   so lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra gives a smooth
   k₁-subalgebra B with fraction field K₁.
4. Smooth base change (lem-weil-pbc-smooth-ring-map-base-change-composition) and smooth ascent
   (lem-weil-pbc-smooth-over-normal-ring-normal) make (k₁ ⊗[k] A) ⊗[k₁] B normal.
5. Localize B at its nonzero elements. By lem-weil-pbc-localization-base-change this localizes
   the tensor algebra; its prime localizations agree with those before localization and are
   normal domains. Tensor associativity identifies the resulting ring with K₁ ⊗[k] A.
6. Tensor associativity and normality descent along K₁/K give normality of K ⊗[k] A.
7. Every extension E/k is the directed union of its finitely generated intermediate fields.
   Tensoring commutes with this colimit by the tensor pushout universal property: compatible
   maps glue on each element in a common finitely generated subfield.
8. Apply lem-weil-pbc-filtered-colimit-normal-ring. For A = 0 all prime-localization conditions
   are vacuous. Universe lifts allow specialization to fields in smaller universes. -/
theorem normal_tensor_perfectClosure_iff
    (k : Type u) (A : Type v) (P : Type w)
    [Field k] [CommRing A] [Algebra k A] [Field P] [Algebra k P] [PerfectField P]
    (hpower : ∀ x : P, ∃ n : ℕ, ∃ a : k, algebraMap k P a = x ^ (ringExpChar k ^ n)) :
    (∀ (p : Ideal (P ⊗[k] A)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
    ∀ (E : Type (max u v w t)) [Field E] [Algebra k E],
      ∀ (p : Ideal (E ⊗[k] A)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end Algebra
