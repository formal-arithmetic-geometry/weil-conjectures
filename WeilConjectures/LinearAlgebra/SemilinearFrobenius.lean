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
as the additive subgroup `LinearMap.Frobenius.fixedPoints F`.

Throughout, `V →ₚ[k, p] W` is local notation for `V →ₛₗ[frobenius k p] W`.

Three basic facts are stated: the fixed points are finite with at most `p ^ dim V` elements;
over an algebraically closed field `v ↦ F v - v` is surjective (Lang–Steinberg); and the fixed
points do not change under an extension of algebraically closed fields.

## Main definitions

- `LinearMap.Frobenius.fixedPoints`: the additive subgroup of fixed points of a `p`-linear map.

## Main statements

- `LinearMap.Frobenius.finite_fixedPoints`, `LinearMap.Frobenius.natCard_fixedPoints_le`:
  the fixed points are finite, of cardinality at most `p ^ Module.finrank k V`.
- `LinearMap.Frobenius.surjective_sub_id`: Lang–Steinberg for `p`-linear maps.
- `LinearMap.Frobenius.existsUnique_baseChange`: a `p`-linear endomorphism has a unique
  `p`-linear base change to `k' ⊗[k] V`.
- `LinearMap.Frobenius.bijective_tmul_fixedPoints`: the fixed points are unchanged by an
  algebraically closed base change.

## Implementation notes

Rather than equipping the fixed points with a `Module (ZMod p)` structure — which is not
available by instance search for a bare `k`-vector space — the dimension bound of
`sk-prop-av-fixed-points` is stated in the equivalent cardinality form
`Nat.card (fixedPoints F) ≤ p ^ Module.finrank k V`.

The base change of `sk-prop-av-fixed-base-change` is written as `k' ⊗[k] V` (rather than
`V ⊗[k] k'`), since that is the side on which Mathlib provides the `k'`-module structure. The
base-changed map `F'` is taken as a hypothesis rather than constructed;
`LinearMap.Frobenius.existsUnique_baseChange` records that exactly one such map exists, so that
the hypothesis is not vacuous.
-/

@[expose] public section

open scoped TensorProduct

namespace LinearMap

namespace Frobenius

/-- `V →ₚ[k, p] W` is the type of `p`-linear (that is, `frobenius k p`-semilinear) maps. -/
local notation:25 V " →ₚ[" k ", " p "] " W => LinearMap (_root_.frobenius k p) V W

variable {k V : Type*} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p] [AddCommGroup V]
  [Module k V]

/-- The additive subgroup of fixed points of a `p`-linear endomorphism `F` of `V`. It is in fact
an `𝔽_p`-subspace, since `F` is additive and fixes the prime field. -/
def fixedPoints (F : V →ₚ[k, p] V) : AddSubgroup V where
  carrier := {v | F v = v}
  zero_mem' := map_zero F
  add_mem' {a b} ha hb := show F (a + b) = a + b by rw [map_add, ha, hb]
  neg_mem' {a} ha := show F (-a) = -a by rw [map_neg, ha]

@[simp]
theorem mem_fixedPoints {F : V →ₚ[k, p] V} {v : V} : v ∈ fixedPoints F ↔ F v = v :=
  Iff.rfl

/-- Blueprint `sk-prop-av-fixed-points`: Fixed points of `p`-linear maps are finite.

Let `k` be a field of characteristic `p > 0`, let `V` be a finite-dimensional `k`-vector space
and let `F : V →ₛₗ[frobenius k p] V` be `p`-linear. Then the fixed points of `F` form a finite
`𝔽_p`-subspace of `V`. -/
instance finite_fixedPoints [FiniteDimensional k V] (F : V →ₚ[k, p] V) :
    Finite (fixedPoints F) :=
  sorry

/-- Blueprint `sk-prop-av-fixed-points`: Fixed points of `p`-linear maps are finite.

The `𝔽_p`-subspace of fixed points of a `p`-linear endomorphism `F` of a finite-dimensional
`k`-vector space `V` has `𝔽_p`-dimension at most `Module.finrank k V`; equivalently, it has at
most `p ^ Module.finrank k V` elements. -/
theorem natCard_fixedPoints_le [FiniteDimensional k V] (F : V →ₚ[k, p] V) :
    Nat.card (fixedPoints F) ≤ p ^ Module.finrank k V :=
  sorry

/-- Blueprint `sk-prop-av-lang-steinberg`: Lang–Steinberg for `p`-linear maps.

Let `k` be an algebraically closed field of characteristic `p > 0`, let `V` be a
finite-dimensional `k`-vector space and let `F : V →ₛₗ[frobenius k p] V` be `p`-linear. Then
`v ↦ F v - v` is surjective. -/
theorem surjective_sub_id [IsAlgClosed k] [FiniteDimensional k V] (F : V →ₚ[k, p] V) :
    Function.Surjective fun v ↦ F v - v :=
  sorry

variable {k' : Type*} [Field k'] [CharP k' p] [Algebra k k']

/-- A `p`-linear endomorphism `F` of `V` has exactly one `p`-linear extension to the base change
`k' ⊗[k] V`, namely `a ⊗ₜ v ↦ a ^ p ⊗ₜ F v`. -/
theorem existsUnique_baseChange (F : V →ₚ[k, p] V) :
    ∃! F' : (k' ⊗[k] V) →ₚ[k', p] (k' ⊗[k] V), ∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v :=
  sorry

/-- Blueprint `sk-prop-av-fixed-base-change`: Fixed points are unchanged by algebraically closed
base change.

Let `k ⊆ k'` be an extension of algebraically closed fields of characteristic `p > 0`, let `V`
be a finite-dimensional `k`-vector space and let `F : V →ₛₗ[frobenius k p] V` be `p`-linear. If
`F'` is a `p`-linear endomorphism of the base change `k' ⊗[k] V` with `F' (1 ⊗ₜ v) = 1 ⊗ₜ F v`
for all `v` — that is, the base change of `F` of `existsUnique_baseChange` — then `v ↦ 1 ⊗ₜ v`
is a bijection from the fixed points of `F` onto the fixed points of `F'`. -/
theorem bijective_tmul_fixedPoints [IsAlgClosed k] [IsAlgClosed k'] [FiniteDimensional k V]
    (F : V →ₚ[k, p] V) (F' : (k' ⊗[k] V) →ₚ[k', p] (k' ⊗[k] V))
    (hF' : ∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v) :
    Function.Bijective fun v : fixedPoints F ↦
      (⟨1 ⊗ₜ[k] (v : V), by rw [mem_fixedPoints, hF', mem_fixedPoints.mp v.2]⟩ :
        fixedPoints F') :=
  sorry

end Frobenius

end LinearMap
