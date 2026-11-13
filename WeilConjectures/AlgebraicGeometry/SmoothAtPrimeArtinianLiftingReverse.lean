/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Basic

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.AlgebraicGeometry.ArtinianLiftingConormalModMaximal

/-!
# Reverse Artinian lifting criterion

A finite type algebra over a Noetherian ring satisfying the lifting property along small
extensions of Artinian local rings at a prime `q` is smooth on an open neighbourhood of `q`.

## Implementation details

The proof uses a localized polynomial presentation and conormal splitting modulo the maximal
ideal. Instead of a completion argument, Mathlib's local finite-free residue-field criterion is
used: a private helper transports the quotient retraction through the tensor/quotient
equivalences, so only reduction modulo the maximal ideal is needed.

## References

* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
* [Stacks Project, Tag 02HS](https://stacks.math.columbia.edu/tag/02HS)
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem residue_injective_of_split_quot
    {S : Type u} [CommRing S] [IsLocalRing S]
    {N : Type v} [AddCommGroup N] [Module S N]
    {M : Type*} [AddCommGroup M] [Module S M]
    (u : N →ₗ[S] M)
    (v : (M ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S M))) →ₗ[S]
      (N ⧸ (IsLocalRing.maximalIdeal S • (⊤ : Submodule S N))))
    (hv : v.comp ((IsLocalRing.maximalIdeal S • (⊤ : Submodule S M)).mkQ.comp u) =
      (IsLocalRing.maximalIdeal S • (⊤ : Submodule S N)).mkQ) :
    Function.Injective (u.lTensor (IsLocalRing.ResidueField S)) := by
  change Function.Injective (u.lTensor (S ⧸ IsLocalRing.maximalIdeal S))
  let eN := TensorProduct.quotTensorEquivQuotSMul N (IsLocalRing.maximalIdeal S)
  let eM := TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal S)
  have h : (eN.symm.toLinearMap.comp (v.comp eM.toLinearMap)).comp
      (u.lTensor (S ⧸ IsLocalRing.maximalIdeal S)) = LinearMap.id := by
    apply TensorProduct.ext'
    intro c x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
      LinearMap.id_apply]
    change eN.symm (v (eM (TensorProduct.tmul S (Ideal.Quotient.mk _ r) (u x)))) = _
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
    have hvr : v (Submodule.Quotient.mk (r • u x)) =
        Submodule.Quotient.mk (r • x) := by
      simpa only [LinearMap.comp_apply, u.map_smul, Submodule.mkQ_apply] using
        LinearMap.congr_fun hv (r • x)
    rw [hvr]
    exact (TensorProduct.quotTensorEquivQuotSMul_mk_tmul _ r x).symm
      |> eN.symm_apply_eq.mpr
  exact Function.HasLeftInverse.injective
    ⟨eN.symm.toLinearMap.comp (v.comp eM.toLinearMap), LinearMap.congr_fun h⟩

set_option backward.isDefEq.respectTransparency false in
/-- Reverse Artinian lifting criterion: if `φ₀ : R →+* A` is of finite type over a Noetherian
ring and every lifting problem along a small extension of Artinian local rings with preimage
maximal ideal `q` is solvable, then `Spec A ⟶ Spec R` is smooth on an open neighbourhood of `q`. -/
theorem artinian_lifting_smooth_on_open_reverse
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    (φ₀ : R →+* A) (hfinite : φ₀.FiniteType) (q : Ideal A) [q.IsPrime] :
    (∀ (B' B : Type (max u v)) [CommRing B'] [CommRing B]
      [IsArtinianRing B'] [IsArtinianRing B] [IsLocalRing B'] [IsLocalRing B]
      (φ : B' →+* B), Function.Surjective φ → Module.length B' (RingHom.ker φ) = 1 →
      ∀ (ρ : R →+* B') (a : A →+* B),
        a.comp φ₀ = φ.comp ρ → Ideal.comap a (IsLocalRing.maximalIdeal B) = q →
        ∃ a' : A →+* B', φ.comp a' = a ∧ a'.comp φ₀ = ρ) →
    (∃ W : (Spec (CommRingCat.of A)).Opens,
      (⟨q, inferInstance⟩ : PrimeSpectrum A) ∈ W ∧
        Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom φ₀))) := by
  classical
  intro hlift
  let := φ₀.toAlgebra
  have : Algebra.FiniteType R A := hfinite
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp
    (inferInstanceAs (Algebra.FiniteType R A))
  let C₀ := MvPolynomial (Fin n) R
  let := π.toRingHom.toAlgebra
  have : IsScalarTower R C₀ A := IsScalarTower.of_algebraMap_eq' π.comp_algebraMap.symm
  let Q := q.comap (algebraMap C₀ A)
  have : Q.IsPrime := Ideal.comap_isPrime _ q
  have : q.LiesOver Q := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver Q q
  let C := Localization.AtPrime Q
  let S := Localization.AtPrime q
  have hsurj : Function.Surjective (algebraMap C S) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    obtain ⟨a', rfl⟩ := hπ a
    obtain ⟨s', hs'⟩ := hπ (s : A)
    have hs'Q : s' ∈ Q.primeCompl := by
      change algebraMap C₀ A s' ∉ q
      exact hs' ▸ s.2
    refine ⟨IsLocalization.mk' C a' ⟨s', hs'Q⟩, ?_⟩
    rw [Localization.AtPrime.algebraMap_eq, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  let P : Algebra.Extension R S :=
    { Ring := C, σ := Function.surjInv hsurj, algebraMap_σ := Function.surjInv_eq hsurj }
  have : Algebra.FormallySmooth C₀ C := .of_isLocalization Q.primeCompl
  have : Algebra.FormallySmooth R C := .comp R C₀ C
  have : Algebra.EssFiniteType C₀ C := .of_isLocalization C Q.primeCompl
  have : Algebra.EssFiniteType R C := .comp R C₀ C
  have : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite
    (IsNoetherian.noetherian P.ker)
  have : Module.Finite S P.CotangentSpace := inferInstance
  have : Module.Free S P.CotangentSpace := Module.free_of_flat_of_isLocalRing
  obtain ⟨v, hv⟩ := Algebra.artinian_lifting_conormal_split_mod_maximal.{u, v} q P hlift
  obtain ⟨l, hl⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective
    P.cotangentComplex).mpr (residue_injective_of_split_quot P.cotangentComplex v hv)
  have : Algebra.IsSmoothAt R q := P.formallySmooth_iff_split_injection.mpr ⟨l, hl⟩
  obtain ⟨g, hg, hsmooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))
  have : Smooth (Spec.map (CommRingCat.ofHom
      ((algebraMap A (Localization.Away g)).comp φ₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    change ((algebraMap A (Localization.Away g)).comp (algebraMap R A)).Smooth
    rw [← IsScalarTower.algebraMap_eq R A (Localization.Away g)]
    exact RingHom.smooth_algebraMap.mpr hsmooth
  have : Smooth (j ≫ Spec.map (CommRingCat.ofHom φ₀)) := by
    change Smooth (Spec.map _ ≫ Spec.map _)
    rw [← Spec.map_comp]
    exact this
  refine ⟨j.opensRange, ?_, ?_⟩
  · change (⟨q, inferInstance⟩ : (Spec (CommRingCat.of A))) ∈ j.opensRange
    rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) g]
    exact hg
  · rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance

end AlgebraicGeometry
