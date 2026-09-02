/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Generators with a common denominator

Let `B` be an `A`-algebra, let `b : B` and let `L` be an arbitrary realization of the
localization of `B` away from `b`. If `L` is of finite type over `A`, its algebra generators
can be chosen to have a single common denominator `b ^ N`: this is
`Algebra.FiniteType.exists_adjoin_mk'_eq_top`, with the equivalent presentation as a surjection
from a polynomial ring in `Algebra.FiniteType.exists_surjective_aeval_mk'`.

The point of allowing an arbitrary `L` rather than `Localization.Away b` is that in geometric
situations the localization arrives as the sections `Γ(X, X.basicOpen b)` of a scheme over a
basic open, which is not `Localization.Away b` on the nose.

Note that `B` is not assumed to be an `A`-algebra: only the composite `A ⟶ L` is needed, and in
the geometric application `A` is the ring of an affine open of the base that receives the basic
open `X_b` but not all of `X`.

Note that no monotonicity lemma is provided: if one wants to enlarge the generating family, the
adjoin form makes this a one-line application of `Algebra.adjoin_mono` combined with
`Set.image_subset`, and `eq_top_iff` (or `top_le_iff`).

We also record that localization away from an idempotent commutes with base change: Mathlib's
`IsLocalization.Away.quotient_of_isIdempotentElem` presents `R ⧸ (1 - e)` as the localization
of `R` away from an idempotent `e`, and `IsLocalization.Away.tensor_quotient_span_one_sub`
says that `A ⊗[S] (R ⧸ (1 - e))` is the localization of `A ⊗[S] R` away from `1 ⊗ e`.
-/

@[expose] public section

open TensorProduct

namespace Algebra.FiniteType

variable {A B : Type*} [CommRing A] [CommRing B] (b : B)
  (L : Type*) [CommRing L] [Algebra B L] [Algebra A L]
  [IsLocalization.Away b L] [Algebra.FiniteType A L]

/-- If a localization `L` of `B` away from `b : B` is of finite type over `A`, then `L` is
generated as an `A`-algebra by finitely many fractions `c / b ^ N` sharing the single
denominator `b ^ N`. -/
theorem exists_adjoin_mk'_eq_top :
    ∃ (N : ℕ) (c : Finset B),
      Algebra.adjoin A
        ((fun x ↦ IsLocalization.mk' L x (⟨b ^ N, N, rfl⟩ : Submonoid.powers b)) '' c) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := ‹Algebra.FiniteType A L›.out
  -- the numerator and the exponent of the denominator of a chosen fraction for `x : L`
  set num : L → B := fun x ↦ (IsLocalization.Away.sec b x).1
  set exp : L → ℕ := fun x ↦ (IsLocalization.Away.sec b x).2
  -- clear all denominators at once, using the largest occurring exponent
  set N : ℕ := s.sup exp
  refine ⟨N, s.image fun x ↦ num x * b ^ (N - exp x), ?_⟩
  have key : ∀ x ∈ s, IsLocalization.mk' L (num x * b ^ (N - exp x))
      (⟨b ^ N, N, rfl⟩ : Submonoid.powers b) = x := by
    intro x hx
    have hxN : exp x ≤ N := Finset.le_sup hx
    have hx' : x = IsLocalization.mk' L (num x) (⟨b ^ exp x, exp x, rfl⟩ : Submonoid.powers b) :=
      IsLocalization.eq_mk'_iff_mul_eq.mpr (IsLocalization.Away.sec_spec b x)
    have hb : b ^ N * num x = b ^ exp x * (num x * b ^ (N - exp x)) := by
      rw [mul_comm (num x), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hxN]
    exact (IsLocalization.mk'_eq_of_eq hb).trans hx'.symm
  rw [← hs]
  congr 1
  rw [Finset.coe_image, Set.image_image]
  simpa using Set.image_congr key

/-- If a localization `L` of `B` away from `b : B` is of finite type over `A`, then `L` is a
quotient of a polynomial ring over `A` in finitely many variables, where the variables are sent
to fractions `c μ / b ^ N` sharing the single denominator `b ^ N`. -/
theorem exists_surjective_aeval_mk' :
    ∃ (N : ℕ) (M : Type) (_ : Finite M) (c : M → B),
      Function.Surjective
        (MvPolynomial.aeval (R := A)
          (fun μ ↦ IsLocalization.mk' L (c μ) (⟨b ^ N, N, rfl⟩ : Submonoid.powers b))) := by
  classical
  obtain ⟨N, c, hc⟩ := exists_adjoin_mk'_eq_top (A := A) b L
  let e : Fin c.card ≃ {x : B // x ∈ c} := (Fintype.equivFinOfCardEq (Fintype.card_coe c)).symm
  refine ⟨N, Fin c.card, inferInstance, fun i ↦ (e i : B), ?_⟩
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  convert hc using 2
  ext y
  simp only [Set.mem_range, Set.mem_image, Finset.mem_coe]
  exact ⟨fun ⟨i, hi⟩ ↦ ⟨e i, (e i).2, hi⟩, fun ⟨x, hx, hy⟩ ↦ ⟨e.symm ⟨x, hx⟩, by simpa using hy⟩⟩

end Algebra.FiniteType

namespace IsLocalization.Away

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra S R] [Algebra S A]
  {e : R}

/-- The `A ⊗[S] R`-algebra structure on `A ⊗[S] (R ⧸ (1 - e))` given by the base change of
the quotient map. -/
@[instance_reducible]
def tensorQuotientAlgebra : Algebra (A ⊗[S] R) (A ⊗[S] (R ⧸ Ideal.span {1 - e})) :=
  (Algebra.TensorProduct.map (AlgHom.id S A) (Ideal.Quotient.mkₐ S (Ideal.span {1 - e}))).toAlgebra

/-- Base change is compatible with localization away from an idempotent: `A ⊗[S] (R ⧸ (1 - e))`
is the localization of `A ⊗[S] R` away from `1 ⊗ e`, with respect to the base change of the
quotient map. This is the base change of Mathlib's
`IsLocalization.Away.quotient_of_isIdempotentElem`. -/
theorem tensor_quotient_span_one_sub (he : IsIdempotentElem e) :
    letI := tensorQuotientAlgebra (S := S) (A := A) (e := e)
    IsLocalization.Away (Algebra.TensorProduct.includeRight e : A ⊗[S] R)
      (A ⊗[S] (R ⧸ Ideal.span {1 - e})) := by
  let inst := tensorQuotientAlgebra (S := S) (A := A) (e := e)
  refine IsLocalization.away_of_isIdempotentElem (he.map _) ?_ ?_
  · rw [RingHom.algebraMap_toAlgebra]
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id S A)
      (Ideal.Quotient.mkₐ S (Ideal.span {1 - e}))) = _
    rw [Algebra.TensorProduct.lTensor_ker _ (Ideal.Quotient.mkₐ_surjective S _)]
    change Ideal.map _ (RingHom.ker (Ideal.Quotient.mk (Ideal.span {1 - e}))) = _
    rw [Ideal.mk_ker, Ideal.map_span, Set.image_singleton, map_sub, map_one]
  · exact Algebra.TensorProduct.map_surjective _ _ Function.surjective_id
      (Ideal.Quotient.mkₐ_surjective S _)

end IsLocalization.Away
