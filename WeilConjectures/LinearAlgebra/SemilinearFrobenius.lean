/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.TensorProduct.Free

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

The proof of `bijective_tmul_fixedPoints` does not use the cyclic-block normal form of the
blueprint. Writing a fixed point of `F'` as `∑ cᵢ ⊗ eᵢ` in a `k`-basis `e` of `V`, the
coordinates satisfy `cⱼ = ∑ᵢ aⱼᵢ cᵢ ^ p` with `aⱼᵢ ∈ k`. A dimension count shows that the `k`-span
of the `cᵢ` in `k'` is stable under `x ↦ x ^ p`, so each `cᵢ` is algebraic over `k`, hence lies
in `k` since `k` is algebraically closed.
-/

@[expose] public section

open scoped TensorProduct

section Auxiliary

open Polynomial

variable {k K : Type*} {p : ℕ} [Field k] [Fact p.Prime] [Field K] [Algebra k K]

/-- An element whose iterated `p`-th powers stay in a finite-dimensional subspace is algebraic. -/
private theorem isAlgebraic_of_pow_pow_mem (W : Submodule k K) [FiniteDimensional k W] {x : K}
    (hx : ∀ i : ℕ, x ^ p ^ i ∈ W) : IsAlgebraic k x := by
  by_contra h
  set d := Module.finrank k W
  have hli : LinearIndependent k (fun i : Fin (d + 1) ↦ (⟨x ^ p ^ (i : ℕ), hx i⟩ : W)) := by
    refine LinearIndependent.of_comp W.subtype ?_
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hq : aeval x (∑ j : Fin (d + 1), C (g j) * X ^ p ^ (j : ℕ)) = 0 := by
      simpa [Algebra.smul_def] using hg
    have h0 := (transcendental_iff.mp h) _ hq
    have := congrArg (coeff · (p ^ (i : ℕ))) h0
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rwa [Finset.sum_eq_single i (fun j _ hj ↦ by
        rw [if_neg]; exact fun e ↦ hj (Fin.ext
          (Nat.pow_right_injective (Fact.out : p.Prime).two_le e).symm))
      (by simp), if_pos rfl] at this
  simpa [d] using hli.fintype_card_le_finrank

/-- Over an algebraically closed field `k`, every element algebraic over `k` lies in `k`. -/
private theorem mem_range_algebraMap_of_isAlgebraic [IsAlgClosed k] {x : K} (hx : IsAlgebraic k x) :
    x ∈ (algebraMap k K).range := by
  have hi := hx.isIntegral
  exact minpoly.mem_range_of_degree_eq_one k x
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))

/-- If every member of a finite family `c` in a field of characteristic `p` is a `k`-linear
combination of the `p`-th powers `c i ^ p`, then the `k`-span `W` of the family is stable under
`x ↦ x ^ p`: indeed `W` lies in the span of the `p`-th powers of a basis of `W`, which has
dimension at most `dim W`. Hence all iterated powers `c j ^ p ^ m` lie in `W`. -/
private theorem pow_pow_mem_span_of_mem_span_pow [CharP K p] {ι : Type*} [Finite ι] {c : ι → K}
    (hc : ∀ j, c j ∈ Submodule.span k (Set.range fun i ↦ c i ^ p)) (j : ι) (m : ℕ) :
    c j ^ p ^ m ∈ Submodule.span k (Set.range c) := by
  set W := Submodule.span k (Set.range c)
  have : FiniteDimensional k W := FiniteDimensional.span_of_finite k (Set.finite_range c)
  set b := Module.finBasis k W
  set U := Submodule.span k (Set.range fun l ↦ (b l : K) ^ p)
  have : FiniteDimensional k U := FiniteDimensional.span_of_finite k (Set.finite_range _)
  have hpow : ∀ x ∈ W, x ^ p ∈ U := by
    intro x hx
    rw [← show ((⟨x, hx⟩ : W) : K) = x from rfl, ← b.sum_repr ⟨x, hx⟩]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def]
    rw [sum_pow_char]
    refine Submodule.sum_mem _ fun l _ ↦ ?_
    rw [mul_pow, ← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hWU : W ≤ U := Submodule.span_le.mpr <| by
    rintro _ ⟨j, rfl⟩
    refine Submodule.span_le.mpr ?_ (hc j)
    rintro _ ⟨i, rfl⟩
    exact hpow _ (Submodule.subset_span ⟨i, rfl⟩)
  have hUW : W = U := Submodule.eq_of_le_of_finrank_le hWU <|
    (finrank_range_le_card _).trans (by simp [W])
  induction m with
  | zero => simpa using (Submodule.subset_span (Set.mem_range_self j) : c j ∈ W)
  | succ m ih => rw [pow_succ, pow_mul]; exact hUW ▸ hpow _ ih

end Auxiliary

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

/-- Blueprint `sk-prop-av-fixed-base-change` (proved as `lem-sc-frobenius-fixed-invariance`):
Fixed points are unchanged by algebraically closed base change.

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
        fixedPoints F') := by
  set b := Module.finBasis k V
  set B := Algebra.TensorProduct.basis k' b
  have hinj : Function.Injective fun v : V ↦ (1 : k') ⊗ₜ[k] v := by
    intro u v huv
    refine b.repr.injective (Finsupp.ext fun i ↦ (algebraMap k k').injective ?_)
    simpa [B] using congrArg (fun w ↦ B.repr w i) huv
  refine ⟨fun u v huv ↦ Subtype.ext (hinj (congrArg Subtype.val huv)), fun w ↦ ?_⟩
  obtain ⟨c, hc⟩ : ∃ c : _ → k', ⇑(B.repr w) = c := ⟨_, rfl⟩
  have key (j) : c j = ∑ i, b.repr (F (b i)) j • c i ^ p := by
    rw [← hc]
    conv_lhs => rw [← mem_fixedPoints.mp w.2, ← B.sum_repr w]
    simp [B, map_sum, hF', Algebra.smul_def, mul_comm]
    rfl
  have := FiniteDimensional.span_of_finite k (Set.finite_range c)
  have hd (j) : c j ∈ (algebraMap k k').range := by
    refine mem_range_algebraMap_of_isAlgebraic (isAlgebraic_of_pow_pow_mem (p := p)
      (Submodule.span k (Set.range c)) (pow_pow_mem_span_of_mem_span_pow (fun j ↦ ?_) j))
    rw [key j]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose d hd using hd
  set v := ∑ j, d j • b j
  have hv : (1 : k') ⊗ₜ[k] v = w := B.repr.injective <| Finsupp.ext fun j ↦ by
    simp [v, B, map_sum, Finsupp.single_apply, hd, ← hc]
  refine ⟨⟨v, hinj ?_⟩, Subtype.ext hv⟩
  change (1 : k') ⊗ₜ[k] F v = 1 ⊗ₜ[k] v
  rw [← hF', hv, mem_fixedPoints.mp w.2]

end Frobenius

end LinearMap
