/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.AdicFieldDifferentialsInjective

/-! # Extension of absolute derivations vanishing on the base maximal ideal

An absolute derivation of `R` into a `T`-module supported at the closed point extends to `T` if
it vanishes on `m_R` and the closed fibre `T/m_R T` is adically formally smooth.

## Implementation details

The derivation descends to `k = R/m_R`. By [Stacks, Tag 07EL] the map
`K ⊗_k Ω_{k/ℤ} → K ⊗_C Ω_{C/ℤ}` (with `C = T/m_R T` and `K` its residue field) is injective,
so the induced functional extends along it using a linear left inverse; composing with the
universal derivation of `C` gives the extension. The construction also works for `M = 0`.

## References

* [Stacks, Tag 07NQ]
* [Stacks, Tag 07EL]
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Derivation

/-- An absolute derivation into a module supported at the closed point extends from
the base if it vanishes on the base maximal ideal and the closed fibre is adically
formally smooth.
formally smooth. -/
theorem exists_extension_of_closedFiber
    (R : Type u) (T : Type v) [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [IsNoetherianRing T]
    [Algebra R T] [IsLocalHom (algebraMap R T)] :
    let L : Ideal T := (maximalIdeal R).map (algebraMap R T)
    letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal R ≤ L.comap (algebraMap R T))
    Algebra.FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
        ((maximalIdeal T).map (Ideal.Quotient.mk L)) →
    ∀ (M : Type w) [AddCommGroup M] [Module T M],
      (∀ x ∈ maximalIdeal T, ∀ m : M, x • m = 0) →
      letI : Module R M := Module.compHom M (algebraMap R T)
      ∀ d : Derivation ℤ R M, (∀ r ∈ maximalIdeal R, d r = 0) →
        ∃ d' : Derivation ℤ T M, ∀ r : R, d' (algebraMap R T r) = d r := by
  intro L hclosed M _ _ hann d hd
  let : Module R M := Module.compHom M (algebraMap R T)
  let k := ResidueField R
  let C := T ⧸ L
  let : Algebra k C := Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.le_comap_map : maximalIdeal R ≤ L.comap (algebraMap R T))
  have hLm : L ≤ maximalIdeal T := by
    rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap]
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top hLm
  let : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr hLtop
  let : IsLocalRing C := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  let : IsNoetherianRing C := isNoetherianRing_of_surjective T C
    (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have hmC : (maximalIdeal T).map (Ideal.Quotient.mk L) = maximalIdeal C :=
    map_maximalIdeal_of_surjective (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective
  have hL : Module.IsTorsionBySet T M L := fun m x ↦ hann x.val (hLm x.property) m
  let : Module C M := hL.module
  let : Module k M := Module.compHom M (algebraMap k C)
  let : IsScalarTower k C M := IsScalarTower.of_compHom k C M
  have hsmul (r : R) (m : M) : (residue R r : k) • m =
      (algebraMap R T r) • m := by
    rfl
  let dbarAdd : k →+ M := QuotientAddGroup.lift (maximalIdeal R).toAddSubgroup
    d.toLinearMap.toAddMonoidHom (fun r hr ↦ hd r hr)
  have hdbar (r : R) : dbarAdd (residue R r) = d r := rfl
  let dbar : Derivation ℤ k M := Derivation.mk' dbarAdd.toIntLinearMap (by
    intro a b
    obtain ⟨a, rfl⟩ := residue_surjective a
    obtain ⟨b, rfl⟩ := residue_surjective b
    change d (a * b) = _
    rw [hsmul, hsmul]
    exact d.leibniz a b)
  have hmc : Module.IsTorsionBySet C M (maximalIdeal C) := by
    intro m x
    have hx : (x : C) ∈ maximalIdeal C := x.property
    have hx' : (x : C) ∈ (maximalIdeal T).map (Ideal.Quotient.mk L) := by
      rwa [hmC]
    obtain ⟨y, hy, he⟩ := (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk L) Ideal.Quotient.mk_surjective).mp hx'
    change x.val • m = 0
    rw [← he]
    exact hann y hy m
  let K := ResidueField C
  let : Module K M := hmc.module
  let : IsScalarTower C K M := hmc.isScalarTower
  let : IsScalarTower k K M := IsScalarTower.of_algebraMap_smul (by
    intro a m
    change (algebraMap C K (algebraMap k C a)) • m = a • m
    rw [IsScalarTower.algebraMap_smul K (algebraMap k C a) m]
    rfl)
  rw [hmC] at hclosed
  let iota := ((KaehlerDifferential.mapBaseChange ℤ k C).baseChange K).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k C K K
      (KaehlerDifferential ℤ k)).symm.toLinearMap
  have hiota : Function.Injective iota :=
    (KaehlerDifferential.residueField_mapBaseChange_injective_of_formallySmoothAdic
      k C hclosed).1
  let phi := (TensorProduct.isBaseChange k (KaehlerDifferential ℤ k) K).lift
    dbar.liftKaehlerDifferential
  let psi := phi.comp iota.leftInverse
  let rho := (psi.restrictScalars C).comp
    (TensorProduct.mk C K (KaehlerDifferential ℤ C) 1)
  let dc : Derivation ℤ C M := rho.compDer (KaehlerDifferential.D ℤ C)
  let : IsScalarTower T C M := hL.isScalarTower
  let dt : Derivation ℤ T M := dc.compAlgebraMap T
  have hiotaD (a : k) :
      iota (TensorProduct.tmul k (1 : K) (KaehlerDifferential.D ℤ k a)) =
        TensorProduct.tmul C (1 : K) (KaehlerDifferential.D ℤ C (algebraMap k C a)) := by
    simp [iota, LinearMap.baseChange_tmul, KaehlerDifferential.mapBaseChange_tmul,
      KaehlerDifferential.map_D]
  have hinv := LinearMap.ker_eq_bot.mpr hiota
  refine ⟨dt, fun r ↦ ?_⟩
  change psi (TensorProduct.tmul C (1 : K)
    (KaehlerDifferential.D ℤ C (algebraMap k C (residue R r)))) = d r
  rw [← hiotaD]
  change phi (iota.leftInverse (iota _)) = d r
  rw [LinearMap.leftInverse_apply_of_inj hinv]
  change phi ((TensorProduct.mk k K (KaehlerDifferential ℤ k) 1)
    (KaehlerDifferential.D ℤ k (residue R r))) = d r
  rw [IsBaseChange.lift_eq, dbar.liftKaehlerDifferential_comp_D]
  exact hdbar r

end Derivation
