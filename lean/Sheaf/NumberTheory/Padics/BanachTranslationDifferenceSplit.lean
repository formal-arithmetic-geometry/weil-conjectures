/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Algebra.Exact.Basic
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Mathlib.Topology.CompactOpen

/-! # The continuously split translation-difference sequence

Source: latest blueprint, six-functors basics, `sk-thm-sf-ctf-stability`, direct-images
proof paragraph (3), analytic expansion of the scalar-cochain argument, steps 4–5.
(blueprint: lem-sfb-banach-translation-difference-split).

The continuous linear arrows below are specified by their pointwise formulas. The Mahler
coordinates are those of `PadicInt.mahlerEquiv_apply`, upgraded from integral to rational
scalar linearity. `ZeroAtInftyContinuousMap ℕ V` is the existing supremum-norm space of
sequences tending to zero. The right inverse is prescribed by conjugating the insertion
of a zero coefficient, with no equivariance requirement on that right inverse.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace PadicInt

/-- The translation-difference sequence on continuous functions on the p-adic integers
is exact, with continuous equivariant arrows, constant kernel identified by evaluation
at zero, and the contractive continuous linear Mahler section. All witnesses are fixed
by the displayed formulas, including the Mahler coefficients and the insertion operator.
Source: latest blueprint, direct-images proof paragraph (3), scalar analytic expansion
(blueprint: lem-sfb-banach-translation-difference-split).

Proof (the six DAG steps):

1. Apply `lem-sfb-integers-profinite-tower` to the degree-one extension of the p-adic
field: the norm topology on its integers is the inverse-limit topology, and the integers
are compact Hausdorff. Addition is continuous by the ultrametric inequality. By
`lem-sfb-compact-function-space-complete`, continuous functions have their complete
supremum norm, whose topology is compact-open.
2. Translation is pointwise linear and isometric since translation of the argument is
bijective. For joint continuity, `lem-coef-compact-open-currying` gives continuous
evaluation on the locally compact p-adic integers; compose evaluation with addition
and curry. The action laws follow from zero and associativity of addition.
3. Difference is translation by one minus the identity, hence continuous and linear.
Constants are a linear isometric injection. Evaluation at zero is continuous and
linear, with norm at most one. Constants are translation invariant; difference commutes
with translation since addition is commutative. These prove equivariance of both arrows.
4. Restrict scalars to the p-adic integers and use `lem-sfb-banach-mahler-coordinates`,
namely `PadicInt.mahlerEquiv` and `PadicInt.mahlerEquiv_apply`. The coefficient formula
proves rational scalar linearity by induction on iterated forward differences. Applying
one extra difference shifts the coefficient sequence by one, also at index zero.
5. Inserting a zero preserves convergence to zero, is linear and isometric; deleting
the first term is contractive and is its left inverse. Conjugate insertion by the
Mahler isometry. This gives the stated section, its norm bound, and surjectivity of
difference. No equivariance of the section is used or asserted.
6. If difference vanishes, all positive Mahler coefficients vanish and the zeroth is
evaluation at zero. Constants have precisely these same coefficients. Injectivity of
the Mahler isometry identifies the kernel with constants; the converse follows by
the difference formula. Evaluation at zero is the continuous inverse on this kernel.
Together with injectivity and surjectivity this proves exactness, also for the zero space.
-/
theorem banach_translation_difference_split (ell : ℕ) [Fact ell.Prime]
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℚ_[ell] V]
    [CompleteSpace V] [IsUltrametricDist V] :
    ∃ (c : V →L[ℚ_[ell]] C(ℤ_[ell], V))
      (d : C(ℤ_[ell], V) →L[ℚ_[ell]] C(ℤ_[ell], V))
      (e : C(ℤ_[ell], V) →L[ℚ_[ell]] V)
      (τ : ℤ_[ell] → C(ℤ_[ell], V) →L[ℚ_[ell]] C(ℤ_[ell], V))
      (M : C(ℤ_[ell], V) ≃ₗᵢ[ℚ_[ell]] ZeroAtInftyContinuousMap ℕ V)
      (P : ZeroAtInftyContinuousMap ℕ V →L[ℚ_[ell]] ZeroAtInftyContinuousMap ℕ V)
      (T : C(ℤ_[ell], V) →L[ℚ_[ell]] C(ℤ_[ell], V)),
      (∀ (v : V) (x : ℤ_[ell]), c v x = v) ∧
      (∀ (f : C(ℤ_[ell], V)) (x : ℤ_[ell]), d f x = f (x + 1) - f x) ∧
      (∀ f : C(ℤ_[ell], V), e f = f 0) ∧
      (∀ (t : ℤ_[ell]) (f : C(ℤ_[ell], V)) (x : ℤ_[ell]), τ t f x = f (x + t)) ∧
      Continuous (fun z : ℤ_[ell] × C(ℤ_[ell], V) ↦ τ z.1 z.2) ∧
      (∀ f : C(ℤ_[ell], V), τ 0 f = f) ∧
      (∀ (s t : ℤ_[ell]) (f : C(ℤ_[ell], V)), τ s (τ t f) = τ (s + t) f) ∧
      (∀ (t : ℤ_[ell]) (v : V), τ t (c v) = c v) ∧
      (∀ (t : ℤ_[ell]) (f : C(ℤ_[ell], V)), d (τ t f) = τ t (d f)) ∧
      Function.Injective c ∧ Function.Exact c d ∧ Function.Surjective d ∧
      (∀ f : C(ℤ_[ell], V), d f = 0 ↔ f = c (e f)) ∧
      (∀ v : V, e (c v) = v) ∧
      (∀ (f : C(ℤ_[ell], V)) (n : ℕ), M f n = (fwdDiff 1)^[n] (⇑f) 0) ∧
      (∀ (f : C(ℤ_[ell], V)) (n : ℕ), M (d f) n = M f (n + 1)) ∧
      (∀ a : ZeroAtInftyContinuousMap ℕ V, P a 0 = 0) ∧
      (∀ (a : ZeroAtInftyContinuousMap ℕ V) (n : ℕ), P a (n + 1) = a n) ∧
      (∀ f : C(ℤ_[ell], V), T f = M.symm (P (M f))) ∧
      (∀ f : C(ℤ_[ell], V), d (T f) = f) ∧
      (∀ f : C(ℤ_[ell], V), ‖T f‖ ≤ ‖f‖) := by
  sorry

end PadicInt
