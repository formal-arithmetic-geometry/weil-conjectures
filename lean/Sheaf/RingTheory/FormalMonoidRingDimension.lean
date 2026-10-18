/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q155
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.HilbertSamuelGrowthDimension

/-!
# Dimension of a formal monoid ring and a parameter hypersurface

Source: ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70;
Stacks Project, Tags 00KQ and 07NV. The explicit dimension input is the
agent-supplied refinement (blueprint: lem-trf-formal-monoid-ring-dimension).
-/

@[expose] public section

universe u v

namespace AddMonoidAlgebra

/-- The completed monoid algebra of a sharp fs monoid over a complete regular local
ring is a Noetherian local domain. Its monomial stratum is the coefficient ring;
its dimension is the coefficient dimension plus the rational rank of the group
completion. Any element reducing to a parameter cuts a hypersurface of dimension
one less, and its coefficient-ring hypersurface is regular local.

Source: ILO VI 1.6(i)--(ii), printed p. 70 (agent-supplied dimension refinement);
Stacks Tags 00KQ, 07NV, 00KW and 00NQ
(blueprint: lem-trf-formal-monoid-ring-dimension).

The equations `ha` and `hL` name exactly the two ideals in the statement.
The `D`-algebra equivalence identifies the stratum with `D` through its canonical
constant inclusion. Thus `e (Ideal.Quotient.mk L η)` is the specified reduction.
The dimension drops are written with `+ 1` to avoid truncated subtraction.

Proof plan:
1. Apply `lem-trf-fs-face-sharpening` to the zero face to identify the group
   completion with a finite free abelian group. Sharpness makes its cone pointed;
   `lem-trf-sharp-monoid-positive-grading` gives a positive integral weight.
   Choose finitely many nonzero monoid generators, allowing the empty list.
2. These generators give a polynomial-algebra surjection onto `D[T]`.
   `lem-weil-pbc-finite-type-algebra-noetherian` and
   `lem-weil-pbc-adic-completion-noetherian` give Noetherianity. Apply
   `lem-trf-monoid-completion-coefficients` to describe the completion by arbitrary
   coefficient families, with finite convolution and the power-filtration formula.
3. Constant coefficient is a surjective ring map with kernel `L`: partition the
   nonzero exponents by a generator dividing them and factor that generator from
   each part. A series is invertible exactly when its constant coefficient is:
   after factoring that unit, the geometric series in the remaining monomials
   converges. Hence the completion is local, with maximal ideal the inverse image
   of the coefficient maximal ideal, and its stratum is canonically `D`.
4. By `lem-sc-regular-local-domain`, `D` is a domain. Order lattice exponents
   lexicographically with the positive weight first. Each bounded-weight set is
   finite, so every nonzero series has a least exponent. The coefficient at the
   sum of two least exponents is the product of their nonzero coefficients.
   Thus the completion is a nonzero domain.
5. The coefficient lemma filters the quotient by the nth maximal-ideal power
   with factors `D / m^(n - ν(t))`, indexed by `ν(t) < n`, where `ν` is maximal
   nonzero-factor length. Their module subobjects agree with their `D`-subobjects.
   `lem-weil-pbc-length-additive-short-exact` computes the length as their sum.
6. If the rank is positive, generator weights bound `ν` above and below by
   constant multiples of weight. Lattice coordinates bound the number of terms
   above by a constant times n to the rank. Independent monoid generators give
   a box of a constant times n to the rank exponents with `ν(t) ≤ n/4`.
   `lem-trf-hilbert-samuel-growth-dimension` for `D` bounds the sum above and
   below by positive multiples of n to the coefficient dimension plus rank.
7. Apply that Hilbert--Samuel theorem also to the completion: comparison of
   polynomial growth degrees gives the dimension formula. Rank zero makes the
   monoid trivial and the completion `D`, so the same formula holds directly.
8. The specified reduction of `η` is nonzero, hence so is `η`; the domain result
   gives injective multiplication. It lies in the maximal ideal by step 3.
   `lem-weil-pbc-dimension-quotient-nonzerodivisor` gives the first dimension drop.
   `lem-weil-pbc-regular-local-hypersurface-criterion` gives regularity of the
   coefficient hypersurface; the same dimension-drop lemma gives its dimension.
   In coefficient dimension zero there is no parameter, so this clause is vacuous.
-/
theorem formalMonoidRing_dimension
    (D : Type u) [CommRing D] [IsRegularLocalRing D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (T : Type v) [AddCommMonoid T]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T))
    (hsharp : ∀ t : T, IsUnit (Multiplicative.ofAdd t) → t = 0)
    (a : Ideal (AddMonoidAlgebra D T))
    (ha : a = Ideal.map (algebraMap D (AddMonoidAlgebra D T))
        (IsLocalRing.maximalIdeal D) ⊔
      Ideal.span {b | ∃ t : T, t ≠ 0 ∧ b = single t (1 : D)})
    (L : Ideal (AdicCompletion a (AddMonoidAlgebra D T)))
    (hL : L = Ideal.span {b | ∃ t : T, t ≠ 0 ∧
      b = AdicCompletion.of a (AddMonoidAlgebra D T) (single t (1 : D))}) :
    IsNoetherianRing (AdicCompletion a (AddMonoidAlgebra D T)) ∧
    IsLocalRing (AdicCompletion a (AddMonoidAlgebra D T)) ∧
    IsDomain (AdicCompletion a (AddMonoidAlgebra D T)) ∧
    ringKrullDim (AdicCompletion a (AddMonoidAlgebra D T)) = ringKrullDim D +
      (Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ
        (Additive (Algebra.GrothendieckGroup (Multiplicative T))))) : WithBot ℕ∞) ∧
    ∃ e : (AdicCompletion a (AddMonoidAlgebra D T) ⧸ L) ≃ₐ[D] D,
      ∀ η : AdicCompletion a (AddMonoidAlgebra D T),
        e (Ideal.Quotient.mk L η) ∈ IsLocalRing.maximalIdeal D →
        e (Ideal.Quotient.mk L η) ∉ (IsLocalRing.maximalIdeal D) ^ 2 →
        Function.Injective (fun x : AdicCompletion a (AddMonoidAlgebra D T) => η * x) ∧
        IsRegularLocalRing (D ⧸ Ideal.span {e (Ideal.Quotient.mk L η)}) ∧
        ringKrullDim ((AdicCompletion a (AddMonoidAlgebra D T)) ⧸ Ideal.span {η}) + 1 =
          ringKrullDim D +
            (Cardinal.toENat (Module.rank ℚ (TensorProduct ℤ ℚ
              (Additive (Algebra.GrothendieckGroup (Multiplicative T))))) : WithBot ℕ∞) ∧
        ringKrullDim (D ⧸ Ideal.span {e (Ideal.Quotient.mk L η)}) + 1 = ringKrullDim D := by
  sorry

end AddMonoidAlgebra
