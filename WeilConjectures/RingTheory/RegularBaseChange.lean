/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GeometricallyRegularFieldExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Regular maps and finite type base change

If `φ : R → Λ` is regular and `R → R'` is of finite type, then `R' → Λ ⊗_R R'` is regular.

## Implementation details

Flatness is preserved by base change. For a prime `p'` of `R'` over `p`, the extension
`κ(p')/κ(p)` is finitely generated, and the new fibre is `κ(p') ⊗_{κ(p)} (κ(p) ⊗_R Λ)`.
Geometric regularity of the original fibre over finitely generated extensions makes this fibre
Noetherian and geometrically regular (also after finite purely inseparable extensions of
`κ(p')`, which are finitely generated over `κ(p)`).

## References

* [Stacks, Tag 07C1]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RingHom

/-- A regular ring map remains regular after base change along a finite type ring map:
if `φ : R → Λ` is regular and `R → R'` is of finite type, then the map
`R' → Λ ⊗_R R'` induced by the second tensor factor is regular. -/
theorem regular_base_change
    {R : Type u} {Λ : Type v} {R' : Type w}
    [CommRing R] [CommRing Λ] [CommRing R'] [Algebra R Λ] [Algebra R R']
    [Algebra.FiniteType R R'] (hφ : (algebraMap R Λ).IsRegular) :
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] Λ ⊗[R] R').toRingHom.IsRegular := by
  classical
  let : Algebra R' (Λ ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  change (algebraMap R' (Λ ⊗[R] R')).IsRegular
  rw [IsRegular, toAlgebra_algebraMap] at hφ ⊢
  have : Module.Flat R Λ := flat_algebraMap_iff.mp hφ.1
  refine ⟨?_, ?_⟩
  · apply flat_algebraMap_iff.mpr
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R R' Λ).symm.toLinearEquiv
  · intro q hq
    let p : Ideal R := q.comap (algebraMap R R')
    have : p.IsPrime := Ideal.comap_isPrime _ q
    have : q.LiesOver p := ⟨rfl⟩
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
    have hp := hφ.2 p
    let e : q.Fiber (Λ ⊗[R] R') ≃ₐ[q.ResidueField]
        q.ResidueField ⊗[p.ResidueField] p.Fiber Λ :=
      (Algebra.TensorProduct.congr (.refl : q.ResidueField ≃ₐ[q.ResidueField] q.ResidueField)
        (Algebra.TensorProduct.commRight R R' Λ).symm).trans
        ((Algebra.TensorProduct.cancelBaseChange R R' q.ResidueField q.ResidueField Λ).trans
          (Algebra.TensorProduct.cancelBaseChange R p.ResidueField
            q.ResidueField q.ResidueField Λ).symm)
    have hfg := IntermediateField.fg_top p.ResidueField q.ResidueField
    have : IsRegularRing (q.ResidueField ⊗[p.ResidueField] p.Fiber Λ) :=
      Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hp q.ResidueField hfg
    have : IsRegularRing (q.Fiber (Λ ⊗[R] R')) :=
      IsRegularRing.of_ringEquiv e.symm.toRingEquiv
    refine ⟨inferInstance, ?_⟩
    intro K _ _ _ _
    let : Algebra p.ResidueField K :=
      (algebraMap q.ResidueField K).comp (algebraMap p.ResidueField q.ResidueField)
        |>.toAlgebra
    have : IsScalarTower p.ResidueField q.ResidueField K :=
      IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
    have : Algebra.EssFiniteType p.ResidueField q.ResidueField := inferInstance
    have : Algebra.EssFiniteType p.ResidueField K :=
      Algebra.EssFiniteType.comp p.ResidueField q.ResidueField K
    have : IsRegularRing (K ⊗[p.ResidueField] p.Fiber Λ) :=
      Algebra.isRegularRing_tensorProduct_of_isGeometricallyRegular hp K
        (IntermediateField.fg_top p.ResidueField K)
    exact IsRegularRing.of_ringEquiv
      ((Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K) e).trans
        (Algebra.TensorProduct.cancelBaseChange p.ResidueField q.ResidueField
          K K (p.Fiber Λ))).symm.toRingEquiv

end RingHom
