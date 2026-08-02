/-
Copyright (c) 2026 Wei Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Yang
-/
import Mathlib

/-!
# Frobenius modules and weights

This file implements the base layer of the weight calculus for the Weil conjectures
(blueprint nodes B1–B2, together with the "no cancellation" kernel used by the
arithmetic pipeline).

A *Frobenius module* over a field `K` is a finite-dimensional `K`-vector space `V`
equipped with a linear automorphism `f : V ≃ₗ[K] V` (thought of as geometric Frobenius
acting on a cohomology group). We deliberately keep the data **unbundled** — all
definitions take `f : V ≃ₗ[K] V` with `[FiniteDimensional K V]` — so that the whole
Mathlib linear-algebra API applies directly; a bundled structure is introduced only
later, where graded families are needed.

## Main definitions

- `Weil.IsEigenvalue f α` : `α` is a root of the characteristic polynomial of `f`.
  This (rather than `Module.End.HasEigenvalue`) is the primitive notion, because the
  arithmetic endgame of the Weil conjectures manipulates characteristic polynomials
  and their root multisets; over an algebraically closed field the two notions agree.
- `Weil.traceIter f n` : the trace of `f ^ n`, the quantity appearing in the
  Grothendieck–Lefschetz trace formula.
- `Weil.IsPureWeight ι q w f`, `Weil.IsMixedLE`, `Weil.IsMixedGE` : purity and
  mixedness bounds of weight `w : ℤ` relative to a field embedding `ι : K →+* ℂ`,
  formulated as `‖ι α‖ ^ 2 = (q : ℝ) ^ w` (squared form: no square roots, no `q^(w/2)`).
- `Weil.IsUnivPureWeight q w f` : purity for **every** `ι : K →+* ℂ`. This is the
  hypothesis actually consumed by the integrality / `ℓ`-independence pipeline; keeping
  the fixed-`ι` and universal notions distinct is a mathematical requirement, not a
  stylistic one (Galois stability of weight classes is quantified over all `ι`).

## Design notes

* Mixedness is defined here by a **bound on all eigenvalues**, not by a filtration
  with pure graded pieces. For a single automorphism of a finite-dimensional space
  over an algebraically closed field the two notions coincide (triangularize), and
  the eigenvalue-bound form makes the Serre-type closure properties consequences of
  elementary root bookkeeping. Filtration-flavoured statements are only needed at the
  sheaf level and will be treated there.
* Weights are integers. Real weights are never needed on the road to the classical
  Weil conjectures, and integer weights make the uniqueness statement
  (`IsPureWeight.weight_eq`) a consequence of injectivity of `n ↦ (q : ℝ) ^ n`.
* The key exported facts are `IsPureWeight.weight_eq` (an object cannot be pure of two
  weights) and `IsPureWeight.not_isEigenvalue_of_ne` (pure objects of distinct weights
  share no eigenvalue) — the latter is the engine behind the coprimality of the odd
  and even parts of the zeta function, hence behind integrality and independence
  of `ℓ`.
-/

universe u v w'

namespace Weil

open Polynomial Module

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w'} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-! ### Eigenvalues via the characteristic polynomial -/

/-- `α` is an eigenvalue of the automorphism `f`, defined as a root of the
characteristic polynomial of the underlying endomorphism. Over an algebraically
closed field this coincides with `Module.End.HasEigenvalue`; we take the
characteristic-polynomial form as primitive because the Weil-conjecture pipeline
is about characteristic polynomials and their root multisets. -/
def IsEigenvalue (f : V ≃ₗ[K] V) (α : K) : Prop :=
  ((f : V →ₗ[K] V).charpoly).IsRoot α

lemma isEigenvalue_iff_det (f : V ≃ₗ[K] V) (α : K) :
    IsEigenvalue f α ↔
      LinearMap.det (algebraMap K (V →ₗ[K] V) α - (f : V →ₗ[K] V)) = 0 := by
  rw [IsEigenvalue, Polynomial.IsRoot, LinearMap.eval_charpoly]

/-- Over an algebraically closed field, a nonzero space has an eigenvalue.
This provides the witness for the weight-uniqueness lemma below. -/
lemma exists_isEigenvalue [IsAlgClosed K] [Nontrivial V] (f : V ≃ₗ[K] V) :
    ∃ α : K, IsEigenvalue f α := by
  apply IsAlgClosed.exists_root
  have h1 : ((f : V →ₗ[K] V).charpoly).natDegree = finrank K V :=
    (f : V →ₗ[K] V).charpoly_natDegree
  have h2 : 0 < ((f : V →ₗ[K] V).charpoly).degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [h1]; exact finrank_pos)
  exact h2.ne'

/-- An automorphism has no eigenvalue `0`. -/
lemma IsEigenvalue.ne_zero {f : V ≃ₗ[K] V} {α : K} (hα : IsEigenvalue f α) :
    α ≠ 0 := by
  rintro rfl
  rw [isEigenvalue_iff_det] at hα
  have hcoe : ((f.trans (LinearEquiv.neg K) : V ≃ₗ[K] V) : V →ₗ[K] V) =
      algebraMap K (V →ₗ[K] V) 0 - (f : V →ₗ[K] V) := by
    ext x
    simp [LinearEquiv.neg]
  exact ((f.trans (LinearEquiv.neg K)).isUnit_det').ne_zero (hcoe ▸ hα)

/-! ### Iterated traces -/

/-- The trace of the `n`-th iterate of `f`. In the realization, `traceIter F n` is the
term `Tr(Fⁿ | Hⁱ)` of the Grothendieck–Lefschetz trace formula. -/
noncomputable def traceIter (f : V ≃ₗ[K] V) (n : ℕ) : K :=
  LinearMap.trace K V ((f : V →ₗ[K] V) ^ n)

@[simp]
lemma traceIter_zero (f : V ≃ₗ[K] V) : traceIter f 0 = (finrank K V : K) := by
  rw [traceIter, pow_zero, LinearMap.trace_one]

omit [FiniteDimensional K V] in
@[simp]
lemma traceIter_one (f : V ≃ₗ[K] V) :
    traceIter f 1 = LinearMap.trace K V (f : V →ₗ[K] V) := by
  rw [traceIter, pow_one]

/-! ### Weight predicates

All predicates are relative to a residue cardinality `q : ℕ` and a field embedding
`ι : K →+* ℂ`. The squared formulation `‖ι α‖ ^ 2 = (q : ℝ) ^ w` avoids both square
roots and half-integer weights. -/

/-- `f` is pure of weight `w` relative to `ι`: every eigenvalue `α` satisfies
`‖ι α‖² = q ^ w`. -/
def IsPureWeight (ι : K →+* ℂ) (q : ℕ) (w : ℤ) (f : V ≃ₗ[K] V) : Prop :=
  ∀ α : K, IsEigenvalue f α → ‖ι α‖ ^ 2 = (q : ℝ) ^ w

/-- `f` is mixed of weights `≤ w` relative to `ι`: every eigenvalue `α` satisfies
`‖ι α‖² ≤ q ^ w`. Over an algebraically closed field this agrees with the existence
of a Frobenius-stable filtration with pure graded pieces of weights `≤ w`. -/
def IsMixedLE (ι : K →+* ℂ) (q : ℕ) (w : ℤ) (f : V ≃ₗ[K] V) : Prop :=
  ∀ α : K, IsEigenvalue f α → ‖ι α‖ ^ 2 ≤ (q : ℝ) ^ w

/-- `f` is mixed of weights `≥ w` relative to `ι`. -/
def IsMixedGE (ι : K →+* ℂ) (q : ℕ) (w : ℤ) (f : V ≃ₗ[K] V) : Prop :=
  ∀ α : K, IsEigenvalue f α → (q : ℝ) ^ w ≤ ‖ι α‖ ^ 2

/-- `f` is pure of weight `w` relative to **every** embedding `ι : K →+* ℂ`.
This universal form is the purity hypothesis of the Weil-conjecture pipeline:
it is exactly what makes weight classes stable under `Aut(K/ℚ)` and hence yields
rational (then integral, then `ℓ`-independent) weight factors. -/
def IsUnivPureWeight (q : ℕ) (w : ℤ) (f : V ≃ₗ[K] V) : Prop :=
  ∀ ι : K →+* ℂ, IsPureWeight ι q w f

variable {ι : K →+* ℂ} {q : ℕ} {w w' : ℤ} {f : V ≃ₗ[K] V} {g : W ≃ₗ[K] W}

lemma IsPureWeight.isMixedLE (h : IsPureWeight ι q w f) : IsMixedLE ι q w f :=
  fun α hα => (h α hα).le

lemma IsPureWeight.isMixedGE (h : IsPureWeight ι q w f) : IsMixedGE ι q w f :=
  fun α hα => (h α hα).ge

lemma isPureWeight_iff_isMixedLE_and_isMixedGE :
    IsPureWeight ι q w f ↔ IsMixedLE ι q w f ∧ IsMixedGE ι q w f :=
  ⟨fun h => ⟨h.isMixedLE, h.isMixedGE⟩,
   fun h α hα => le_antisymm (h.1 α hα) (h.2 α hα)⟩

lemma IsUnivPureWeight.isPureWeight (h : IsUnivPureWeight q w f) (ι : K →+* ℂ) :
    IsPureWeight ι q w f :=
  h ι

/-- Upper weight bounds are monotone in the bound. -/
lemma IsMixedLE.mono (hq : 1 ≤ q) (hww' : w ≤ w') (h : IsMixedLE ι q w f) :
    IsMixedLE ι q w' f := by
  intro α hα
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  calc ‖ι α‖ ^ 2 ≤ (q : ℝ) ^ w := h α hα
    _ ≤ (q : ℝ) ^ w' := by gcongr

/-- Lower weight bounds are antitone in the bound. -/
lemma IsMixedGE.mono (hq : 1 ≤ q) (hww' : w' ≤ w) (h : IsMixedGE ι q w f) :
    IsMixedGE ι q w' f := by
  intro α hα
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  calc (q : ℝ) ^ w' ≤ (q : ℝ) ^ w := by gcongr
    _ ≤ ‖ι α‖ ^ 2 := h α hα

section Injectivity

variable (hq : 1 < q)
include hq

private lemma zpow_injective :
    Function.Injective fun n : ℤ => (q : ℝ) ^ n :=
  zpow_right_injective₀ (by positivity)
    (by exact_mod_cast hq.ne')

/-- **Disjointness of weights.** Two automorphisms that are pure of *different*
weights (relative to the same `ι`) have no common eigenvalue. Applied to the graded
pieces of cohomology, this is the "no cancellation between weights" step: it makes
the odd and even parts of the zeta function coprime, which is what allows the
individual factors `Pᵢ` to be recovered from the integral zeta function. -/
lemma IsPureWeight.not_isEigenvalue_of_ne (hww' : w ≠ w')
    (hf : IsPureWeight ι q w f) (hg : IsPureWeight ι q w' g)
    {α : K} (hα : IsEigenvalue f α) : ¬ IsEigenvalue g α := fun hα' =>
  hww' (zpow_injective hq ((hf α hα).symm.trans (hg α hα')))

/-- **Uniqueness of the weight.** On a nonzero space over an algebraically closed
field, an automorphism cannot be pure of two different weights. -/
lemma IsPureWeight.weight_eq [IsAlgClosed K] [Nontrivial V]
    (h : IsPureWeight ι q w f) (h' : IsPureWeight ι q w' f) : w = w' := by
  obtain ⟨α, hα⟩ := exists_isEigenvalue f
  exact zpow_injective hq ((h α hα).symm.trans (h' α hα))

/-- Universal-purity version of weight uniqueness. The `Nonempty (K →+* ℂ)`
hypothesis is satisfied by `K = ℚ̄_ℓ` (an algebraically closed field of
characteristic zero and cardinality continuum). -/
lemma IsUnivPureWeight.weight_eq [IsAlgClosed K] [Nontrivial V]
    [Nonempty (K →+* ℂ)] {f : V ≃ₗ[K] V}
    (h : IsUnivPureWeight q w f) (h' : IsUnivPureWeight q w' f) : w = w' := by
  obtain ⟨ι⟩ := ‹Nonempty (K →+* ℂ)›
  exact (h ι).weight_eq hq (h' ι)

end Injectivity

end Weil
