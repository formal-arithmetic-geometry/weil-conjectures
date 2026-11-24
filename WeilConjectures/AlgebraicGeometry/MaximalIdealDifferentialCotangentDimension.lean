/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Etale.Kaehler

/-!
# The cotangent dimension at a closed point over an algebraically closed field

## References

* [Stacks, Algebra, Tag 00TR](https://stacks.math.columbia.edu/tag/00TR)
* [Stacks, Algebra, Tag 00RT](https://stacks.math.columbia.edu/tag/00RT)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- The differential fibre has the dimension of the cotangent space of the local ring.
(Stacks, Tags 00TR, 00RT) -/
theorem finrank_cotangentSpace_atMaximal_eq_differentials
    (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S]
    [IsAlgClosed k] [Algebra.FiniteType k S]
    (m : Ideal S) (hm : m.IsMaximal) :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime m))
        (IsLocalRing.CotangentSpace (Localization.AtPrime m)) =
      Module.finrank m.ResidueField (TensorProduct S m.ResidueField
        (KaehlerDifferential k S)) := by
  classical
  let R := Localization.AtPrime m
  let K := m.ResidueField
  have : Algebra.FiniteType k K :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom k S K)
      m.algebraMap_residueField_surjective
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let s : K →ₐ[k] R := (Algebra.ofId k R).comp e.symm.toAlgHom
  let s₂ : K →ₐ[k] (R ⧸ RingHom.ker (algebraMap R K) ^ 2) :=
    (Ideal.Quotient.mkₐ k _).comp s
  have hs₂ : (IsScalarTower.toAlgHom k R K).kerSquareLift.comp s₂ = AlgHom.id k K := by
    apply AlgHom.ext
    intro a
    obtain ⟨a, rfl⟩ := e.surjective a
    simp [s₂, s, e]
  let ret := (retractionKerCotangentToTensorEquivSection
    (R := k) (P := R) (S := K) (IsLocalRing.residue_surjective)).symm ⟨s₂, hs₂⟩
  have hinj : Function.Injective (KaehlerDifferential.kerCotangentToTensor k R K) := by
    apply Function.LeftInverse.injective (g := ret.val)
    exact fun x ↦ LinearMap.congr_fun ret.property x
  have : Subsingleton (KaehlerDifferential k K) :=
    KaehlerDifferential.subsingleton_of_surjective k K e.surjective
  have hsurj : Function.Surjective (KaehlerDifferential.kerCotangentToTensor k R K) := by
    intro x
    exact (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k R K
      IsLocalRing.residue_surjective x).mp (Subsingleton.elim _ _)
  let ec := Ideal.Cotangent.equivOfEq (IsLocalRing.maximalIdeal R)
    (RingHom.ker (algebraMap R K)) IsLocalRing.ker_residue.symm
  let ecot := (ec.trans (LinearEquiv.ofBijective
    (KaehlerDifferential.kerCotangentToTensor k R K) ⟨hinj, hsurj⟩)).extendScalarsOfSurjective
      (IsLocalRing.residue_surjective (R := R))
  have : Algebra.FormallyEtale S R := Algebra.FormallyEtale.of_isLocalization m.primeCompl
  let eloc := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k S R
  let efibre := (TensorProduct.AlgebraTensorModule.congr (.refl K K) eloc.symm).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S R K K (KaehlerDifferential k S))
  exact ecot.finrank_eq.trans efibre.finrank_eq

end Algebra
