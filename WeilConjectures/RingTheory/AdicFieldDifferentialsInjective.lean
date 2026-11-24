/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.RingTheory.DifferentialsInjectiveOfH1CotangentInjectiveCharP
import WeilConjectures.RingTheory.FormallySmoothAdicGeometricallyRegular
import Mathlib.RingTheory.Smooth.Field
import WeilConjectures.RingTheory.GeometricallyRegularH1Injective

/-!
# Base-field differentials of an adically formally smooth local algebra

Let `C` be a Noetherian local `k`-algebra with residue field `K`, formally smooth for the
`m`-adic topology. We show that `K ⊗[k] Ω[k⁄ℤ] → K ⊗[C] Ω[C⁄ℤ]` is injective.

## Implementation details

In characteristic zero, `K / k` is formally smooth, so already `K ⊗[k] Ω[k⁄ℤ] → Ω[K⁄ℤ]` is
injective, and this map factors through `K ⊗[C] Ω[C⁄ℤ]`. In characteristic `p`, `C` is
geometrically regular over `k`, so the map `H₁(L_{K/k}) → m/m²` is injective, which gives the
injectivity for differentials over `ZMod p`; these agree with differentials over `ℤ`.

The tensor factors are written as `K ⊗[k] Ω[k⁄ℤ]` (rather than `Ω[k⁄ℤ] ⊗[k] K`), using the
canonical symmetry.

## References

* Stacks Project, Tag 07EL, (2) implies (5); Tag 07NQ, final proof paragraph; Tag 0322.
-/

@[expose] public section

universe u v

namespace KaehlerDifferential

private theorem primeField_bijective (p : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [CharP R p] :
    letI := ZMod.algebra R p
    Function.Bijective (map ℤ (ZMod p) R R) := by
  let := ZMod.algebra R p
  let : Subsingleton (KaehlerDifferential ℤ (ZMod p)) :=
    subsingleton_of_surjective ℤ (ZMod p) ZMod.intCast_surjective
  refine ⟨?_, map_surjective ℤ (ZMod p) R⟩
  rw [← LinearMap.ker_eq_bot, ← range_mapBaseChange ℤ (ZMod p) R]
  exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)

private theorem charZero_injective (k : Type u) (K : Type v)
    [Field k] [Field K] [Algebra k K] [CharZero k] :
    Function.Injective (mapBaseChange ℤ k K) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  let := hs.isAlgebraic_field
  have : Algebra.FormallySmooth k K :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  exact (LinearMap.injective_iff_eq_zero_of_exact
    (Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ k K)).mpr (Subsingleton.elim _ _)

/-- Let `C` be a Noetherian local `k`-algebra, formally smooth for its maximal-ideal-adic
topology, with residue field `K`. Then the canonical map `K ⊗[k] Ω[k⁄ℤ] → K ⊗[C] Ω[C⁄ℤ]` is
injective. In characteristic zero its composition with the map to `Ω[K⁄ℤ]` is still injective,
and in characteristic `p` the canonical maps from differentials over `ℤ` to differentials over
`ZMod p` are bijective for `k` and `C`. -/
theorem residueField_mapBaseChange_injective_of_formallySmoothAdic
    (k : Type u) (C : Type v) [Field k] [CommRing C] [Algebra k C]
    [IsLocalRing C] [IsNoetherianRing C]
    (h : Algebra.FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)) :
    let K := IsLocalRing.ResidueField C
    let iota := ((mapBaseChange ℤ k C).baseChange K).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange k C K K
        (KaehlerDifferential ℤ k)).symm.toLinearMap
    Function.Injective iota ∧
      (∀ [CharZero k], Function.Injective ((mapBaseChange ℤ C K).comp iota)) ∧
      (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        letI : CharP C p :=
          charP_of_injective_algebraMap (algebraMap k C).injective p
        letI := ZMod.algebra k p
        letI := ZMod.algebra C p
        Function.Bijective (map ℤ (ZMod p) k k) ∧
          Function.Bijective (map ℤ (ZMod p) C C)) := by
  let K := IsLocalRing.ResidueField C
  let iota := ((mapBaseChange ℤ k C).baseChange K).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k C K K
      (KaehlerDifferential ℤ k)).symm.toLinearMap
  have hiota (x : K) (y : KaehlerDifferential ℤ k) :
      iota (TensorProduct.tmul k x y) = TensorProduct.tmul C x (map ℤ ℤ k C y) := by
    simp [iota, LinearMap.baseChange_tmul, mapBaseChange_tmul]
  have hcomp : (mapBaseChange ℤ C K).comp iota = mapBaseChange ℤ k K := by
    have hm : ((map ℤ ℤ C K).restrictScalars k).comp (map ℤ ℤ k C) =
        map ℤ ℤ k K := by
      apply Derivation.liftKaehlerDifferential_unique
      ext a
      change map ℤ ℤ C K (map ℤ ℤ k C (D ℤ k a)) = map ℤ ℤ k K (D ℤ k a)
      simp only [map_D]
      rw [← IsScalarTower.algebraMap_apply k C K]
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    simp only [LinearMap.comp_apply, hiota, mapBaseChange_tmul]
    exact congrArg (x • ·) (LinearMap.congr_fun hm y)
  have hzero [CharZero k] : Function.Injective ((mapBaseChange ℤ C K).comp iota) := by
    rw [hcomp]
    exact charZero_injective k K
  refine ⟨?_, (by intro _; exact hzero), ?_⟩
  · obtain ⟨p, hp⟩ := CharP.exists k
    let : CharP k p := hp
    rcases CharP.char_is_prime_or_zero k p with hp | rfl
    · let : Fact p.Prime := ⟨hp⟩
      let := ZMod.algebra k p
      let := ((algebraMap k C).comp (algebraMap (ZMod p) k)).toAlgebra
      let lambdaMap := (TensorProduct.isBaseChange k (KaehlerDifferential (ZMod p) k) K).lift
        (((TensorProduct.mk C K (KaehlerDifferential (ZMod p) C) 1).restrictScalars k).comp
          (map (ZMod p) (ZMod p) k C))
      have hlambda : Function.Injective lambdaMap :=
        Algebra.differentials_injective_of_h1Cotangent_injective_charP k C p
          (Algebra.isRegularLocalRing_and_injective_h1Cotangent_of_isGeometricallyRegular
            k C p (Algebra.isGeometricallyRegular_of_formallySmoothAdic k C h)).2
      let f := (map ℤ (ZMod p) k k).lTensor K
      let g := (map ℤ (ZMod p) C C).lTensor K
      have hf : Function.Injective f :=
        Module.Flat.lTensor_preserves_injective_linearMap _ (primeField_bijective p k).1
      have hm : ((map ℤ (ZMod p) C C).restrictScalars k).comp (map ℤ ℤ k C) =
          (map (ZMod p) (ZMod p) k C).comp (map ℤ (ZMod p) k k) := by
        apply Derivation.liftKaehlerDifferential_unique
        ext a
        change map ℤ (ZMod p) C C (map ℤ ℤ k C (D ℤ k a)) =
          map (ZMod p) (ZMod p) k C (map ℤ (ZMod p) k k (D ℤ k a))
        simp only [map_D, Algebra.algebraMap_self_apply]
      have hlambda_tmul (x : K) (y : KaehlerDifferential (ZMod p) k) :
          lambdaMap (TensorProduct.tmul k x y) =
            TensorProduct.tmul C x (map (ZMod p) (ZMod p) k C y) := by
        have hy : lambdaMap (TensorProduct.tmul k 1 y) =
            TensorProduct.tmul C 1 (map (ZMod p) (ZMod p) k C y) :=
          IsBaseChange.lift_eq _ _ y
        calc
          lambdaMap (TensorProduct.tmul k x y) = lambdaMap (x • (TensorProduct.tmul k 1 y)) := by
            congr 1
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          _ = x • lambdaMap (TensorProduct.tmul k 1 y) := map_smul _ _ _
          _ = TensorProduct.tmul C x (map (ZMod p) (ZMod p) k C y) := by
            rw [hy, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hsquare (x : TensorProduct k K (KaehlerDifferential ℤ k)) :
          g (iota x) = lambdaMap (f x) := by
        induction x using TensorProduct.inductionOn with
        | tmul x y =>
          simp only [hiota, g, f, LinearMap.lTensor_tmul]
          rw [hlambda_tmul]
          exact congrArg (fun z ↦ TensorProduct.tmul C x z) (LinearMap.congr_fun hm y)
        | add x y hx hy => simp only [map_add, hx, hy]
      intro x y hxy
      apply hf
      apply hlambda
      rw [← hsquare, ← hsquare, hxy]
    · let : CharZero k := CharP.charP_to_charZero k
      exact Function.Injective.of_comp (f := mapBaseChange ℤ C K) hzero
  · intro p _ _
    let : CharP C p := charP_of_injective_algebraMap (algebraMap k C).injective p
    exact ⟨primeField_bijective p k, primeField_bijective p C⟩

end KaehlerDifferential
