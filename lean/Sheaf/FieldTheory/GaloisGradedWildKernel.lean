/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Index
public import Sheaf.RingTheory.ValuationComapResidue
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.PGroup

/-!
# The wild kernel of the action on initial forms

Source: Temkin, Stable modification of relative curves, §2.1, Lemma 2.1.5;
Gabber–Ramero, Almost Ring Theory, sixth release, §6.2.8–6.2.18,
especially Proposition 6.2.12 and Corollary 6.2.14
(blueprint: lem-trf-galois-graded-wild-kernel).

The existentially bound rings, fields and integers are specified by equalities;
they abbreviate canonical objects without any choice of a residue embedding.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ValuationSubring

/-- The initial-form kernel is normal and wild, and its fixed field is tame.
Source: Temkin, §2.1, Lemma 2.1.5; Gabber–Ramero, sixth release, §6.2.8–6.2.18,
Proposition 6.2.12 and Corollary 6.2.14
(blueprint: lem-trf-galois-graded-wild-kernel).

Proof plan:
1. Embed any finite separable extension into a finite Galois extension using
   lem-weil-pbc-finite-galois-receiving-separable-extensions. Uniqueness of the extending
   absolute value (lem-sfb-algebraic-absolute-value-unique) makes every automorphism an
   isometry. The inequality defining P is stable under products, inverses and conjugation.
   The finite-Galois fixed-field theorem makes the automorphism group finite.
2. If a prime q differs from the residue characteristic, its norm is one. For an element
   sigma of P of order q, the averaging operator A(y) = sum sigma^i(y) has norm equal to
   that of y, hence is injective. But A(z - sigma(z)) = 0, so sigma is the identity.
   Cauchy's theorem excludes every such prime divisor of the order of P. Thus its order
   is a p-power in positive residue characteristic and is one in characteristic zero.
3. Put m = card P. The orbit product b(x) = product rho(x) over P lies in T and satisfies
   |b(x) - x^m| < |x|^m, |b(x)| = |x|^m. For units its residue is the m-th power of x's.
4. The valued-extension degree bound makes the relative value group and residue degree
   finite. The orbit product kills the upper value-group quotient by m and puts every
   residue m-th power in the lower residue field. Apply the finite-group prime-power
   cardinality lemma and the purely-inseparable p-th-root tower lemma. For p = 0, P = 1
   and T = N, so the upper residue map is surjective and both upper invariants are one.
5. By the normal-fixed-quotient theorem, restriction identifies G/P with Aut_K(T), whose
   order is [T:K] by the finite-Galois fixed-field theorem. Its elements are isometries.
6. Lift an automorphism of T in its initial-form kernel to sigma in G. Applying it to
   b(x) shows that the residue of sigma(x)/x has m-th power one. Since m is a p-power
   (or one in characteristic zero), the residue is one. Hence sigma belongs to P, and
   the original automorphism of T is the identity.
7. Apply lem-trf-valued-initial-form-automorphism-bound to T/K and this trivial kernel.
   Together with lem-trf-valued-extension-degree-bound this gives
   e f ≤ [T:K] = |Aut_K(T)| ≤ e' s ≤ e f. Equality implies residue separability,
   e prime to p when p > 0, and [T:K] = e f. No discrete or perfect-residue hypothesis
   is used. -/
theorem galois_graded_wild_kernel
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (hext : ∀ (F : Type (max u v w)) [Field F] [Algebra K F] [FiniteDimensional K F],
      ∃ a : AbsoluteValue F ℝ, ∀ x : K, a (algebraMap K F x) = ‖x‖) :
    (∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
        [Algebra.IsSeparable K L],
      ∃ (M : Type (max u v)) (_ : Field M) (_ : Algebra K M),
        FiniteDimensional K M ∧ IsGalois K M ∧ Nonempty (L →ₐ[K] M)) ∧
    (∀ (N : Type w) [NormedField N] [IsUltrametricDist N] [Algebra K N]
        [FiniteDimensional K N] [IsGalois K N],
      (∀ x : K, ‖algebraMap K N x‖ = ‖x‖) →
      ∃ (P : Subgroup (N ≃ₐ[K] N)) (T : IntermediateField K N)
        (O : ValuationSubring N) (B : ValuationSubring T) (p e f e₁ f₁ : ℕ),
        O = (NormedField.valuation (K := N)).valuationSubring ∧
        B = O.comap (algebraMap T N) ∧
        T = IntermediateField.fixedField P ∧
        (∀ σ : N ≃ₐ[K] N, σ ∈ P ↔ ∀ x : N, x ≠ 0 → ‖σ x - x‖ < ‖x‖) ∧
        P.Normal ∧
        p = ringChar (IsLocalRing.ResidueField (O.comap (algebraMap K N))) ∧
        e = ((QuotientGroup.mk' B.unitGroup).comp
          (Units.map (algebraMap K T).toMonoidHom)).range.index ∧
        f = @Module.finrank (IsLocalRing.ResidueField (B.comap (algebraMap K T)))
          (IsLocalRing.ResidueField B) _ _
          (B.comapResidueAlgebra (algebraMap K T)).toModule ∧
        e₁ = ((QuotientGroup.mk' O.unitGroup).comp
          (Units.map (algebraMap T N).toMonoidHom)).range.index ∧
        f₁ = @Module.finrank (IsLocalRing.ResidueField (O.comap (algebraMap T N)))
          (IsLocalRing.ResidueField O) _ _
          (O.comapResidueAlgebra (algebraMap T N)).toModule ∧
        @Algebra.IsSeparable (IsLocalRing.ResidueField (B.comap (algebraMap K T)))
          (IsLocalRing.ResidueField B) _ _ (B.comapResidueAlgebra (algebraMap K T)) ∧
        Module.finrank K T = e * f ∧
        (0 < p → (∃ a : ℕ, Nat.card P = p ^ a) ∧ Nat.Coprime e p ∧
          (∀ z : IsLocalRing.ResidueField O, ∃ a : ℕ,
            z ^ (p ^ a) ∈ Set.range (O.comapResidueFieldMap (algebraMap T N))) ∧
          (∃ a : ℕ, e₁ = p ^ a) ∧ ∃ a : ℕ, f₁ = p ^ a) ∧
        (p = 0 → P = ⊥ ∧
          Function.Surjective (O.comapResidueFieldMap (algebraMap T N)) ∧
          e₁ = 1 ∧ f₁ = 1)) := by
  sorry

end ValuationSubring
