/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# `p`-linear endomorphisms of vector spaces in characteristic `p`

Let `k` be a field of characteristic `p > 0` and `V` a `k`-vector space. A *`p`-linear*
endomorphism of `V` is a semilinear map `F : V →ₛₗ[frobenius k p] V`, that is, an additive map
with `F (a • v) = a ^ p • F v`. Its fixed points form an `𝔽_p`-subspace of `V`, recorded here
as the additive subgroup `LinearMap.frobeniusFixedPoints F`.

Three basic facts are stated: the fixed points are finite with at most `p ^ dim V` elements;
over an algebraically closed field `v ↦ F v - v` is surjective (Lang–Steinberg); and the fixed
points do not change under an extension of algebraically closed fields.

## Main definitions

- `LinearMap.frobeniusFixedPoints`: the additive subgroup of fixed points of a `p`-linear map.

## Main statements

- `LinearMap.finite_frobeniusFixedPoints`, `LinearMap.natCard_frobeniusFixedPoints_le`:
  the fixed points are finite, of cardinality at most `p ^ Module.finrank k V`.
- `LinearMap.surjective_sub_id`: Lang–Steinberg for `p`-linear maps.
- `LinearMap.bijective_tmul_frobeniusFixedPoints`: the fixed points are unchanged by an
  algebraically closed base change.

## Implementation notes

Rather than equipping the fixed points with a `Module (ZMod p)` structure — which is not
available by instance search for a bare `k`-vector space — the dimension bound of
`sk-prop-av-fixed-points` is stated in the equivalent cardinality form
`Nat.card (frobeniusFixedPoints F) ≤ p ^ Module.finrank k V`.

The base change of `sk-prop-av-fixed-base-change` is written as `k' ⊗[k] V` (rather than
`V ⊗[k] k'`), since that is the side on which Mathlib provides the `k'`-module structure, and
the base change `F'` of `F` is not constructed: it is taken as an arbitrary
`frobenius k' p`-semilinear endomorphism satisfying `F' (1 ⊗ₜ v) = 1 ⊗ₜ F v`.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

variable {k V : Type*} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p] [AddCommGroup V]
  [Module k V]

/-- The additive subgroup of fixed points of a `p`-linear endomorphism `F` of `V`. It is in fact
an `𝔽_p`-subspace, since `F` is additive and fixes the prime field. -/
def frobeniusFixedPoints (F : V →ₛₗ[_root_.frobenius k p] V) : AddSubgroup V where
  carrier := {v | F v = v}
  zero_mem' := map_zero F
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_neg, ha]

@[simp]
theorem mem_frobeniusFixedPoints {F : V →ₛₗ[_root_.frobenius k p] V} {v : V} :
    v ∈ frobeniusFixedPoints F ↔ F v = v :=
  Iff.rfl

/-- Blueprint `sk-prop-av-fixed-points`: Fixed points of `p`-linear maps are finite.

Let `k` be a field of characteristic `p > 0`, let `V` be a finite-dimensional `k`-vector space
and let `F : V →ₛₗ[frobenius k p] V` be `p`-linear. Then the fixed points of `F` form a finite
`𝔽_p`-subspace of `V`. -/
theorem finite_frobeniusFixedPoints [FiniteDimensional k V] (F : V →ₛₗ[_root_.frobenius k p] V) :
    Finite (frobeniusFixedPoints F) :=
  sorry

/-- Blueprint `sk-prop-av-fixed-points`: Fixed points of `p`-linear maps are finite.

The `𝔽_p`-subspace of fixed points of a `p`-linear endomorphism `F` of a finite-dimensional
`k`-vector space `V` has `𝔽_p`-dimension at most `Module.finrank k V`; equivalently, it has at
most `p ^ Module.finrank k V` elements. -/
theorem natCard_frobeniusFixedPoints_le [FiniteDimensional k V]
    (F : V →ₛₗ[_root_.frobenius k p] V) :
    Nat.card (frobeniusFixedPoints F) ≤ p ^ Module.finrank k V :=
  sorry

/-- Blueprint `sk-prop-av-lang-steinberg`: Lang–Steinberg for `p`-linear maps.

Let `k` be an algebraically closed field of characteristic `p > 0`, let `V` be a
finite-dimensional `k`-vector space and let `F : V →ₛₗ[frobenius k p] V` be `p`-linear. Then
`v ↦ F v - v` is surjective. -/
theorem surjective_sub_id [IsAlgClosed k] [FiniteDimensional k V]
    (F : V →ₛₗ[_root_.frobenius k p] V) :
    Function.Surjective fun v => F v - v :=
  sorry

variable {k' : Type*} [Field k'] [CharP k' p] [Algebra k k']

/-- Blueprint `sk-prop-av-fixed-base-change`: Fixed points are unchanged by algebraically closed
base change.

Let `k ⊆ k'` be an extension of algebraically closed fields of characteristic `p > 0`, let `V`
be a finite-dimensional `k`-vector space and let `F : V →ₛₗ[frobenius k p] V` be `p`-linear. If
`F'` is a `p`-linear endomorphism of the base change `k' ⊗[k] V` with `F' (1 ⊗ₜ v) = 1 ⊗ₜ F v`
for all `v`, then `v ↦ 1 ⊗ₜ v` is a bijection from the fixed points of `F` onto the fixed
points of `F'`. -/
theorem bijective_tmul_frobeniusFixedPoints [IsAlgClosed k] [IsAlgClosed k']
    [FiniteDimensional k V] (F : V →ₛₗ[_root_.frobenius k p] V)
    (F' : (k' ⊗[k] V) →ₛₗ[_root_.frobenius k' p] (k' ⊗[k] V))
    (hF' : ∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v) :
    Function.Bijective fun v : frobeniusFixedPoints F =>
      (⟨1 ⊗ₜ[k] (v : V), by rw [mem_frobeniusFixedPoints, hF', mem_frobeniusFixedPoints.mp v.2]⟩ :
        frobeniusFixedPoints F') :=
  sorry

end LinearMap
