/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.RingTheory.CompletionFiniteExtensionDecomposition
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Completed fibre presentation for a specified finite coefficient extension

Base-changing a completed polynomial fibre along a finite coefficient extension `A → B` gives a
finite product of completed fibres of `B[X]`.

## Implementation details

The completion of `B[X]` along `q` is the product of the completions at the primes over `q`.
Factors at primes not containing `s` vanish after tensoring with `κ(s)`, since an element of `s`
outside the prime is a unit there; the remaining primes are enumerated by `Fin n`.

## References

* [Stacks, Tag 07PU] (first paragraph of the proof)
* [Stacks, Tag 07N9]
-/

@[expose] public section

universe u

namespace Polynomial

/-- Base-changing a completed polynomial fibre through a specified finite coefficient
extension gives the product indexed by primes over `q` which contain the specified `s`.
The residue-field equivalence must commute with the original polynomial map. -/
theorem completed_fibre_compatible_product
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A] [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing B] [IsLocalRing B]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A)
    (r : Ideal (Polynomial A)) [r.IsPrime]
    (L : Type u) [Field L] [Algebra r.ResidueField L]
    (s : Ideal (Polynomial B)) [s.IsPrime] [Algebra B L]
    (e : s.ResidueField ≃ₐ[B] L)
    (he : ∀ f : Polynomial A,
      e (algebraMap (Polynomial B) s.ResidueField
        (Polynomial.map (algebraMap A B) f)) =
        algebraMap r.ResidueField L (algebraMap (Polynomial A) r.ResidueField f)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)
    ∃ (n : ℕ) (q' : Fin n → Ideal (Polynomial B))
      (qmax : ∀ i, (q' i).IsMaximal),
      letI := qmax
      (∀ i, (q' i).comap (Polynomial.C : B →+* Polynomial B) =
        IsLocalRing.maximalIdeal B) ∧
      (∀ i, s ≤ q' i) ∧
      Nonempty ((TensorProduct r.ResidueField L (r.Fiber C)) ≃+*
        (∀ i : Fin n, s.Fiber
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime (q' i)))
            (Localization.AtPrime (q' i))))) := by
  classical
  let : Algebra (Polynomial A) (Polynomial B) := Polynomial.algebra A B
  let ep : (TensorProduct A (Polynomial A) B) ≃ₐ[Polynomial A] Polynomial B :=
    { (Algebra.TensorProduct.comm A (Polynomial A) B).toRingEquiv.trans
        (polyEquivTensor A B).symm.toRingEquiv with
      commutes' := by
        intro f
        simp [polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.algebraMap_def] }
  have : Module.Finite (Polynomial A) (Polynomial B) :=
    Module.Finite.equiv ep.toLinearEquiv
  let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    (Localization.AtPrime q)
  let Q := q.primesOver (Polynomial B)
  let D := fun t : Q ↦
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime t.1))
      (Localization.AtPrime t.1)
  obtain ⟨hfin, E, _, _, _⟩ :=
    AdicCompletion.completion_finite_extension_decomposition (Polynomial A) (Polynomial B) q
  have : Finite Q := hfin
  let : Fintype Q := Fintype.ofFinite Q
  have hcontract (t : Q) : t.1.comap (Polynomial.C : B →+* Polynomial B) =
      IsLocalRing.maximalIdeal B := by
    have hcomp : (t.1.comap (Polynomial.C : B →+* Polynomial B)).comap
        (algebraMap A B) = IsLocalRing.maximalIdeal A := by
      calc
        _ = (t.1.comap (algebraMap (Polynomial A) (Polynomial B))).comap
            (Polynomial.C : A →+* Polynomial A) := by
          rw [Ideal.comap_comap, Ideal.comap_comap]
          rw [Polynomial.algebraMap_def, Polynomial.mapRingHom_comp_C]
        _ = _ := by
          change (t.1.under (Polynomial A)).comap Polynomial.C = _
          rw [← Ideal.LiesOver.over (P := t.1) (p := q)]
          exact hq
    apply IsLocalRing.eq_maximalIdeal
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
    change ((t.1.comap (Polynomial.C : B →+* Polynomial B)).comap
      (algebraMap A B)).IsMaximal
    rw [hcomp]
    infer_instance
  let : Algebra (Polynomial A) L :=
    ((algebraMap r.ResidueField L).comp (algebraMap (Polynomial A) r.ResidueField)).toAlgebra
  have : IsScalarTower (Polynomial A) r.ResidueField L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (Polynomial B) L :=
    (e.toRingHom.comp (algebraMap (Polynomial B) s.ResidueField)).toAlgebra
  have : IsScalarTower (Polynomial A) (Polynomial B) L :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun f ↦ (he f).symm)
  let er : s.ResidueField ≃ₐ[Polynomial A] L :=
    { e.toRingEquiv with
      commutes' := by
        intro f
        rw [IsScalarTower.algebraMap_apply (Polynomial A) (Polynomial B) s.ResidueField]
        exact he f }
  let E₁ := Algebra.TensorProduct.cancelBaseChange (Polynomial A) r.ResidueField L L C
  let E₂ := Algebra.TensorProduct.congr er (.refl : C ≃ₐ[Polynomial A] C)
  let E₃ := Algebra.TensorProduct.cancelBaseChange (Polynomial A) (Polynomial B)
    s.ResidueField s.ResidueField C
  let : Algebra (Polynomial B) (TensorProduct (Polynomial A) C (Polynomial B)) :=
    Algebra.TensorProduct.rightAlgebra
  let E₄ := Algebra.TensorProduct.congr (.refl : s.ResidueField ≃ₐ[s.ResidueField] s.ResidueField)
    (Algebra.TensorProduct.commRight (Polynomial A) (Polynomial B) C)
  let E₅ := Algebra.TensorProduct.congr (.refl : s.ResidueField ≃ₐ[s.ResidueField] s.ResidueField) E
  let E₆ := Algebra.TensorProduct.piRight (Polynomial B) s.ResidueField s.ResidueField D
  let efull : (TensorProduct r.ResidueField L (r.Fiber C)) ≃+* (∀ t : Q, s.Fiber (D t)) :=
    E₁.toRingEquiv.trans (E₂.symm.toRingEquiv.trans
    (E₃.symm.toRingEquiv.trans (E₄.toRingEquiv.trans
      (E₅.toRingEquiv.trans E₆.toRingEquiv))))
  have hzero (t : Q) (h : ¬ s ≤ t.1) : Subsingleton (s.Fiber (D t)) := by
    obtain ⟨x, hxs, hxt⟩ := IsConcreteLE.not_le_iff_exists.mp h
    have hu : IsUnit (algebraMap (Polynomial B) (D t) x) := by
      rw [IsScalarTower.algebraMap_apply (Polynomial B) (Localization.AtPrime t.1) (D t)]
      exact (IsLocalization.map_units (Localization.AtPrime t.1) (⟨x, hxt⟩ : t.1.primeCompl)).map _
    have hz : algebraMap (Polynomial B) (s.Fiber (D t)) x = 0 := by
      rw [IsScalarTower.algebraMap_apply (Polynomial B) s.ResidueField (s.Fiber (D t))]
      rw [Ideal.algebraMap_residueField_eq_zero.mpr hxs, map_zero]
    have hu' := hu.map
      (Algebra.TensorProduct.includeRight : D t →ₐ[Polynomial B] s.Fiber (D t))
    rw [AlgHom.commutes, hz] at hu'
    exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu')
  let U := {t : Q // s ≤ t.1}
  let restrict : (∀ t : Q, s.Fiber (D t)) →+* (∀ t : U, s.Fiber (D t.1)) :=
    { toFun := fun f t ↦ f t.1
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hinj : Function.Injective restrict := by
    intro f g h
    funext t
    by_cases ht : s ≤ t.1
    · exact congrFun h ⟨t, ht⟩
    · have := hzero t ht
      exact Subsingleton.elim _ _
  have hsurj : Function.Surjective restrict := by
    intro f
    refine ⟨fun t ↦ if ht : s ≤ t.1 then f ⟨t, ht⟩ else 0, ?_⟩
    funext t
    exact dite_eq_left t.2
  let E₇ := RingEquiv.ofBijective restrict ⟨hinj, hsurj⟩
  let en : Fin (Fintype.card U) ≃ U := (Fintype.equivFin U).symm
  refine ⟨Fintype.card U, fun i ↦ (en i).1.1, fun i ↦ inferInstance, ?_, ?_, ?_⟩
  · intro i
    exact hcontract (en i).1
  · intro i
    exact (en i).2
  · exact ⟨efull.trans (E₇.trans
      (RingEquiv.piCongrLeft (fun t : U ↦ s.Fiber (D t.1)) en).symm)⟩

end Polynomial
