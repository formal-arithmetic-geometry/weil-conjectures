/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Base change of a simple degree-p field presentation

If `L = M(z)` with `z ^ p = a ∈ M` and `[L : M] = p`, then for every `K`-algebra `F` the ring
`L ⊗_K F` is the quotient of `(M ⊗_K F)[Z]` by `Z ^ p - a ⊗ 1`.

## Implementation details

The polynomial `X ^ p - a` is the minimal polynomial of `z`, so `M[Z] / (Z ^ p - a) ≃ L`; this
presentation is base changed along `M → M ⊗_K F`, using tensor associativity on the target.

## References

* [Stacks, Tag 07PR]
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- If `L = M(z)` with `z ^ p = a ∈ M` and `[L : M] = p`, then
`(M ⊗_K F)[Z] / (Z ^ p - a ⊗ 1)` is isomorphic as a ring to `L ⊗_K F`. -/
theorem nonempty_quotient_X_pow_sub_C_ringEquiv_tensorProduct
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (M : IntermediateField K L)
    (F : Type u) [CommRing F] [Algebra K F]
    (p : ℕ) [Fact p.Prime] (z : L)
    (hz : IntermediateField.adjoin M ({z} : Set L) = ⊤)
    (a : M) (ha : z ^ p = (a : L)) (hdeg : Module.finrank M L = p) :
    Nonempty ((Polynomial (TensorProduct K M F) ⧸
      Ideal.span ({Polynomial.X ^ p - Polynomial.C
                    (Algebra.TensorProduct.includeLeftRingHom a)} :
          Set (Polynomial (TensorProduct K M F)))) ≃+* TensorProduct K L F) := by
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hm : (Polynomial.X ^ p - Polynomial.C a).Monic :=
    Polynomial.monic_X_pow_sub_C a hp
  have hv : Polynomial.aeval z (Polynomial.X ^ p - Polynomial.C a) = 0 := by
    simp [ha]
  have hi : IsIntegral M z := ⟨_, hm, hv⟩
  have hd : (minpoly M z).natDegree = p := by
    have h := IntermediateField.adjoin.finrank hi
    rw [hz, IntermediateField.finrank_top'] at h
    exact h.symm.trans hdeg
  have he : minpoly M z = Polynomial.X ^ p - Polynomial.C a := by
    symm
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hm
    · exact minpoly.dvd M z hv
    · rw [Polynomial.natDegree_X_pow_sub_C, hd]
  let e : AdjoinRoot (Polynomial.X ^ p - Polynomial.C a) ≃ₐ[M] L :=
    (AdjoinRoot.algEquivOfEq M _ _ he.symm).trans
      ((IntermediateField.adjoinRootEquivAdjoin M hi).trans
        ((IntermediateField.equivOfEq hz).trans IntermediateField.topEquiv))
  let q : Polynomial (TensorProduct K F M) :=
    Polynomial.X ^ p - Polynomial.C (Algebra.TensorProduct.includeRight a)
  let eb := AdjoinRoot.tensorAlgEquiv (R := K) (T := F)
    (Polynomial.X ^ p - Polynomial.C a) q (by simp [q])
  let ec := Algebra.TensorProduct.comm K F M
  let eq := AdjoinRoot.mapRingEquiv ec.toRingEquiv q
    (Polynomial.X ^ p - Polynomial.C
      (Algebra.TensorProduct.includeLeftRingHom a))
    (by
      apply Associated.of_eq
      simp [q, ec])
  let et := Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[F] F) (e.restrictScalars K)
  exact ⟨eq.symm.trans (eb.symm.toRingEquiv.trans
    (et.toRingEquiv.trans (Algebra.TensorProduct.comm K F L).toRingEquiv))⟩

end MvPowerSeries
