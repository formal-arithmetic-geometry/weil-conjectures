/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.AnalyticallyUnramified
public import WeilConjectures.RingTheory.JapaneseDomain
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Analytically unramified local domains are N-1

A Noetherian local domain with reduced completion is N-1.

## Implementation details

The completion `B` is a reduced complete local ring, hence Nagata, so the product `P` of the
integral closures of its domain quotients by minimal primes is finite over `B`. By flatness,
`R' ⊗ B` embeds into the total ring of fractions of `B`, with image in `P`, where `R'` is the
integral closure of `R`; hence `R' ⊗ B` is finite over `B`, and faithful flatness shows that
`R'` is finite over `R`.

## References

* [Stacks, Tag 032Y]
-/

@[expose] public section

universe u v

private theorem finite_reduced_nagata_normalization (B : Type u)
    [CommRing B] [IsReduced B] (hB : IsNagataRing B) :
    Module.Finite B (integralClosure B (FractionRing B)) := by
  classical
  let : IsNoetherianRing B := hB.1
  obtain ⟨t, q, _, _, hres, _, hmaps, hbij⟩ :=
    reduced_noetherian_total_ring_fractions (R := B)
  choose φ hφ huniq using hmaps
  let ψ (i : Fin t) : FractionRing B →ₐ[B] (q i).1.asIdeal.ResidueField :=
    { toRingHom := (algebraMap (Localization.AtPrime (q i).1.asIdeal)
        (q i).1.asIdeal.ResidueField).comp (φ i)
      commutes' b := by
        change algebraMap _ _ (φ i (algebraMap B (FractionRing B) b)) = _
        have hi := RingHom.congr_fun (hφ i) b
        change φ i (algebraMap B (FractionRing B) b) = _ at hi
        rw [hi]
        exact (IsScalarTower.algebraMap_apply B
          (Localization.AtPrime (q i).1.asIdeal) (q i).1.asIdeal.ResidueField b).symm }
  let P (i : Fin t) :=
    integralClosure (B ⧸ (q i).1.asIdeal) (q i).1.asIdeal.ResidueField
  have hP (i : Fin t) : Module.Finite B (P i) := by
    let D := B ⧸ (q i).1.asIdeal
    let E := (q i).1.asIdeal.ResidueField
    have hD : Module.Finite D (integralClosure D (FractionRing D)) :=
      isN1_of_isN2 D (FractionRing D) (hB.2 (q i).1.asIdeal)
    let e : FractionRing D ≃ₐ[D] E := IsLocalization.algEquiv (nonZeroDivisors D) _ _
    let : Module.Finite D (integralClosure D E) :=
      Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv
    exact Module.Finite.trans D (P i)
  let : ∀ i : Fin t, Module.Finite B (P i) := hP
  let j : integralClosure B (FractionRing B) →ₗ[B] (∀ i : Fin t, P i) :=
    { toFun := fun x i ↦ ⟨ψ i x.val, (x.prop.map (ψ i)).tower_top⟩
      map_add' := by
        intro x y
        ext i
        exact map_add (ψ i) x.val y.val
      map_smul' := by
        intro b x
        ext i
        exact (ψ i).toLinearMap.map_smul b x.val }
  apply Module.Finite.of_injective j
  intro x y hxy
  apply Subtype.ext
  apply (hbij φ hφ).1
  funext i
  apply (hres i).1
  exact congrArg Subtype.val (congrFun hxy i)

private theorem finite_tensor_normalization
    (R : Type u) (K : Type v) (B : Type u)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Module.Flat R B] [IsNoetherianRing B]
    [Module.Finite B (integralClosure B (FractionRing B))] :
    Module.Finite B (TensorProduct R B (integralClosure R K)) := by
  let T := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  have hT : T ≤ nonZeroDivisors B := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hr
    simpa [Algebra.smul_def, mul_comm] using hb
  have hu (t : T) : IsUnit (algebraMap B (FractionRing B) t) :=
    IsLocalization.map_units (FractionRing B) (⟨t.1, hT t.2⟩ : nonZeroDivisors B)
  let f : TensorProduct R B K →ₐ[B] FractionRing B :=
    IsLocalization.liftAlgHom (f := Algebra.ofId B (FractionRing B)) hu
  have hf : Function.Injective f := by
    apply (IsLocalization.lift_injective_iff hu).mpr
    intro x y
    rw [(IsLocalization.injective (TensorProduct R B K) hT).eq_iff,
      (IsFractionRing.injective B (FractionRing B)).eq_iff]
  let g : TensorProduct R B (integralClosure R K) →ₐ[B] TensorProduct R B K :=
    Algebra.TensorProduct.map (AlgHom.id B B) (integralClosure R K).val
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (integralClosure R K).val.toLinearMap Subtype.val_injective
  let j := f.comp g
  let k : TensorProduct R B (integralClosure R K) →ₐ[B] integralClosure B (FractionRing B) :=
    j.codRestrict (integralClosure B (FractionRing B)) fun x ↦
      (Algebra.IsIntegral.isIntegral x).map j
  exact Module.Finite.of_injective k.toLinearMap fun x y hxy ↦
    hg (hf (congrArg Subtype.val hxy))


/-- A Noetherian local integral domain whose maximal-ideal-adic completion is reduced
has finite integral closure in its fraction field, hence is N-1. -/
theorem isN1_of_isAnalyticallyUnramified (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (h : IsAnalyticallyUnramified R) : IsN1 R K := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing _
  let : IsReduced B := h
  have hB : IsNagataRing B := isNagataRing_of_complete_local B
  let : Module.Finite B (integralClosure B (FractionRing B)) :=
    finite_reduced_nagata_normalization B hB
  let : Module.Finite B (TensorProduct R B (integralClosure R K)) :=
    finite_tensor_normalization R K B
  let : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B
