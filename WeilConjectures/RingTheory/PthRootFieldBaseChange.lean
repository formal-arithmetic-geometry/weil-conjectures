/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import WeilConjectures.RingTheory.PthRootFieldQuotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Field.ULift

/-! # The p-root quotient as base change by a field

If the coefficients have independent differentials, the `p`-root quotient over `A` is the base
change of `A` by a finite purely inseparable field extension of `k`.

## Implementation details

The `p`-root quotient `Q` over `k` is a finite field with all `p`-th powers in `k`, hence purely
inseparable; `F = ULift Q` meets the universe bound. The polynomial and quotient tensor
equivalences identify `A ⊗_k Q` with the quotient over `A`. The quotient is constructed
explicitly, and no regularity, locality or Noetherianity of `A` is needed.

## References

* [Stacks, Tag 07E5] (proof of (2) ⇒ (4))
* [Stacks, Tag 07DZ]
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Independent coefficient differentials identify the actual p-root quotient with
base change by a finite purely inseparable field extension. -/
theorem pthRootAlgebra_equiv_field_baseChange
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ) (a : Fin n → k) :
    letI := ZMod.algebra k p
    LinearIndependent k (fun i ↦ KaehlerDifferential.D (ZMod p) k (a i)) →
    ∃ (F : Type (max u v)) (hF : Field F),
      letI := hF
      ∃ (hAlg : Algebra k F),
        letI := hAlg
        Module.Finite k F ∧ IsPurelyInseparable k F ∧
          Nonempty (pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i)) ≃ₐ[A]
            (A ⊗[k] F))  := by
  classical
  intro hind
  let P := MvPolynomial (Fin n) k
  let I : Ideal P := Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : P) ^ p - MvPolynomial.C (a i)))
  let Q := pthRootAlgebra p n k a
  obtain ⟨hfield, hfinite, hpow⟩ := pthRootAlgebra_isField_finite_pow k p n a hind
  let : Field Q := hfield.toField
  let := hfinite
  have : IsPurelyInseparable k Q := (isPurelyInseparable_iff_pow_mem k p).mpr
    (fun x ↦ ⟨1, by simpa using hpow x⟩)
  let F := ULift.{v} Q
  let eF : F ≃ₐ[k] Q := ULift.algEquiv
  have hfinF : Module.Finite k F :=
    Module.Finite.of_surjective eF.symm.toLinearMap eF.symm.surjective
  have hpureF : IsPurelyInseparable k F := eF.symm.isPurelyInseparable
  let f : A ⊗[k] P ≃ₐ[A] MvPolynomial (Fin n) A :=
    MvPolynomial.algebraTensorAlgEquiv k A
  let J : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range (fun i : Fin n ↦
    (MvPolynomial.X i : MvPolynomial (Fin n) A) ^ p -
      MvPolynomial.C (algebraMap k A (a i))))
  have hIJ : J = (I.map (TensorProduct.includeRight (A := A)).toRingHom).map
      f.toRingHom := by
    rw [Ideal.map_map (TensorProduct.includeRight (R := k) (A := A) (B := P)).toRingHom
      f.toRingHom]
    dsimp only [I, J]
    rw [Ideal.map_span]
    apply congrArg Ideal.span
    rw [← Set.range_comp]
    congr 1
    funext i
    change MvPolynomial.X i ^ p - MvPolynomial.C (algebraMap k A (a i)) =
      f (1 ⊗ₜ[k] (MvPolynomial.X i ^ p - MvPolynomial.C (a i)))
    have h := (MvPolynomial.algebraTensorAlgEquiv_tmul k A 1
      (MvPolynomial.X i ^ p - MvPolynomial.C (a i))).symm
    rw [one_smul, map_sub, map_pow, MvPolynomial.map_X, MvPolynomial.map_C] at h
    exact h
  let eQ : A ⊗[k] Q ≃ₐ[A]
      pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i)) :=
    (TensorProduct.tensorQuotientEquiv (R := k) A P A I).trans
      (Ideal.quotientEquivAlg _ J f hIJ)
  let e : pthRootAlgebra p n A (fun i ↦ algebraMap k A (a i)) ≃ₐ[A] A ⊗[k] F :=
    eQ.symm.trans (TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eF.symm)
  exact ⟨F, inferInstance, inferInstance, hfinF, hpureF, ⟨e⟩⟩

end Algebra
