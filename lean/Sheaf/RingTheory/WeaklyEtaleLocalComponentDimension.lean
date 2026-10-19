/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.RingTheory.IndPrincipalZariski
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.RingTheory.RingKrullDimLeOfFaithfullyFlatOfIsLocalHom
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Sheaf.RingTheory.WeaklyEtaleDimension
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Finite
import Sheaf.RingTheory.NormalizationLocalizationDimension
import Sheaf.RingTheory.WeaklyEtaleNormalization

/-! # Dimensions of local components under a weakly etale homomorphism

Source: Silvio Greco, Two theorems on excellent rings (1976), Lemma 5.5,
printed p. 147, with the introduction's Noetherian convention and Remark 5.2
(blueprint: lem-exc-weakly-etale-local-component-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingHom.WeaklyEtale

/-- Every minimal component of a local weakly etale algebra over a universally catenary
local domain with finite normalization has the dimension of that domain.
Source: Greco, Two theorems on excellent rings (1976), Lemma 5.5, printed p. 147;
Remark 5.2 identifies AF with weak etaleness for Noetherian rings
(blueprint: lem-exc-weakly-etale-local-component-dimension).

Proof:
1. Put A = D/P, C' = the normalization of C, H = C' tensor_C D, and E = the
   normalization of A. The normalization-tensor theorem identifies H with the
   normalization of D and splits E off as a D-algebra factor. Its projection t is
   surjective and sends 1 tensor d to the image of d in E. Finite generators of C'
   base change to generators of H over D and project to generators of E over D,
   hence over A. The integral injective inclusions give dim E = dim A and dim C' = dim C.
2. Base change makes H weakly etale over C'. The proved dimension upper bound for
   weakly etale algebras gives dim H <= dim C'. Surjectivity of t gives dim E <= dim H.
   These facts give dim A <= dim C without choosing a chain of maximal length.
3. Choose any maximal ideal n of the domain E, and let m be its contraction to C'.
   The map C' -> E is flat: C' -> H is weakly etale and H -> E is, up to the
   normalization equivalences, the product projection, a localization at (1,0).
   The finite extension A -> E contracts n to the maximal ideal of A; the quotient
   D -> A and the original local map C -> D show that m contracts to the maximal
   ideal of C. Integrality of C -> C' then makes m maximal. The finite-normalization
   dimension theorem gives dim C'_m = dim C.
4. The canonical local map C'_m -> E_n is flat, hence faithfully flat. Thus
   dim C = dim C'_m <= dim E_n <= dim E = dim A. The second inequality is the
   height bound for localization at a prime. Combine with step 2.
-/
theorem ringKrullDim_quotient_minimalPrime_eq
    {C : Type u} {D : Type v} [CommRing C] [CommRing D]
    [IsNoetherianRing C] [IsLocalRing C] [IsDomain C]
    [IsNoetherianRing D] [IsLocalRing D]
    [Module.Finite C (integralClosure C (FractionRing C))]
    (f : C →+* D) [IsLocalHom f] (hf : f.WeaklyEtale)
    (hC : IsUniversallyCatenary C) (P : Ideal D) (hP : P ∈ minimalPrimes D) :
    ringKrullDim (D ⧸ P) = ringKrullDim C := by
  let : Algebra C D := f.toAlgebra
  have : Algebra.WeaklyEtale C D := hf
  have : IsLocalHom (algebraMap C D) := ‹IsLocalHom f›
  have : P.IsPrime := hP.isPrime
  let A := D ⧸ P
  have : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk P) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let C' : Type u := integralClosure C (FractionRing C)
  let E : Type v := integralClosure A (FractionRing A)
  let H := TensorProduct C C' D
  obtain ⟨_, ⟨e₀, _⟩, hs⟩ := @weaklyEtale_normalization_tensor C _ _ hC _ _ _ D _ _ _
    (f.toAlgebra) ‹IsLocalHom (algebraMap C D)› ‹Algebra.WeaklyEtale C D›
  obtain ⟨F, aF, e₁, he₁⟩ := hs P hP
  let : Algebra D H := Algebra.TensorProduct.rightAlgebra
  let : Algebra D (E × F) :=
    (RingHom.prod ((algebraMap A E).comp (Ideal.Quotient.mk P)) (algebraMap D F)).toAlgebra
  let t : H →+* E := (RingHom.fst E F).comp (e₁.toRingHom.comp e₀.toRingHom)
  have ht : Function.Surjective t :=
    Prod.fst_surjective.comp (e₁.toRingEquiv.surjective.comp e₀.surjective)
  have htD (d : D) :
      t (TensorProduct.tmul C (1 : C') d) = algebraMap A E (Ideal.Quotient.mk P d) := by
    have hh := e₀.commutes d
    change e₀ (TensorProduct.tmul C (1 : C') d) = _ at hh
    change (e₁ (e₀ (TensorProduct.tmul C (1 : C') d))).1 = _
    rw [hh]
    exact he₁ d
  let : Algebra D E := ((algebraMap A E).comp (Ideal.Quotient.mk P)).toAlgebra
  have : IsScalarTower D A E := .of_algebraMap_eq fun _ ↦ rfl
  let tD : H →ₗ[D] E :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := fun d x ↦ by
        change t ((TensorProduct.tmul C (1 : C') d) * x) =
          algebraMap A E (Ideal.Quotient.mk P d) * t x
        rw [map_mul, htD] }
  have : Module.Finite D H := by
    let e := (Algebra.TensorProduct.commRight C D C').toLinearEquiv
    exact Module.Finite.equiv e
  have : Module.Finite D E := Module.Finite.of_surjective tD ht
  have : Module.Finite A E := Module.Finite.of_restrictScalars_finite D A E
  have hEA : ringKrullDim E = ringKrullDim A := ringKrullDim_eq_of_isIntegral A E
  have hHC : ringKrullDim H ≤ ringKrullDim C' :=
    Algebra.WeaklyEtale.ringKrullDim_le (R := C') (S := H)
  have hC'C : ringKrullDim C' = ringKrullDim C := ringKrullDim_eq_of_isIntegral C C'
  apply le_antisymm
  · change ringKrullDim A ≤ ringKrullDim C
    rw [← hEA, ← hC'C]
    exact (ringKrullDim_le_of_surjective t ht).trans hHC
  · obtain ⟨n, hn⟩ := Ideal.exists_maximal E
    have : n.IsMaximal := hn
    let g : C' →+* E := t.comp (algebraMap C' H)
    have hg : g.Flat := by
      have htflat : t.Flat := by
        apply RingHom.Flat.comp
          (RingHom.Flat.comp (.of_bijective e₀.bijective) (.of_bijective e₁.toRingEquiv.bijective))
        let : Algebra (E × F) E := (RingHom.fst E F).toAlgebra
        exact IsLocalization.flat E (Submonoid.powers ((1 : E), (0 : F)))
      exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) htflat
    let m := n.comap g
    have hmC : m.comap (algebraMap C C') = IsLocalRing.maximalIdeal C := by
      have hnA : n.comap (algebraMap A E) = IsLocalRing.maximalIdeal A :=
        IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n)
      have hnD : n.comap (algebraMap D E) = IsLocalRing.maximalIdeal D := by
        change (n.comap (algebraMap A E)).comap (Ideal.Quotient.mk P) = _
        rw [hnA]
        exact IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk P)
      have hcomp : g.comp (algebraMap C C') = (algebraMap D E).comp f := by
        apply RingHom.ext
        intro c
        change t (algebraMap C' H (algebraMap C C' c)) = _
        rw [← IsScalarTower.algebraMap_apply C C' H,
          IsScalarTower.algebraMap_apply C D H]
        exact htD (f c)
      change n.comap (g.comp (algebraMap C C')) = _
      rw [hcomp]
      change (n.comap (algebraMap D E)).comap f = _
      rw [hnD, IsLocalRing.maximalIdeal_comap]
    have : m.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap m
      (hmC.symm ▸ (inferInstance : (IsLocalRing.maximalIdeal C).IsMaximal))
    have hdim := hC.ringKrullDim_localization_integralClosure_eq m hmC
    let g' := Localization.localRingHom m n g rfl
    have : IsLocalHom g' := Localization.isLocalHom_localRingHom m n g rfl
    have hg' : g'.Flat := hg.localRingHom n m rfl
    let : Algebra (Localization.AtPrime m) (Localization.AtPrime n) := g'.toAlgebra
    have : Module.Flat (Localization.AtPrime m) (Localization.AtPrime n) := hg'
    have : Module.FaithfullyFlat (Localization.AtPrime m) (Localization.AtPrime n) :=
      .of_flat_of_isLocalHom
    have hle := RingHom.ringKrullDim_le_of_faithfullyFlat_of_isLocalHom g'
      (show g'.FaithfullyFlat from
        (inferInstance : Module.FaithfullyFlat (Localization.AtPrime m) (Localization.AtPrime n)))
    rw [hdim] at hle
    change ringKrullDim C ≤ ringKrullDim A
    rw [← hEA]
    apply hle.trans
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height n]
    exact n.height_le_ringKrullDim_of_isPrime

end RingHom.WeaklyEtale
